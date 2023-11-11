import "./sanity.spec";

/// @dev Verify on original contract:
/// certoraRun certora/confs/EBTCToken_verified.conf
/// @dev Verify against mutations:
/// certoraMutate --prover_conf certora/confs/EBTCToken_verified.conf --mutation_conf certora/confs/gambit/EBTCToken.conf

/* -------------------------------------------------------------------------- */
/*                                   METHODS                                  */
/* -------------------------------------------------------------------------- */

methods {
    function call_isBOOrCdpMOrAuth(address user, bytes4 functionSig) external returns (bool) envfree;
    function call_isValidTransfer(address from, address to) external returns (bool) envfree;
    function cdpManagerAddress() external returns (address) envfree;
    function borrowerOperationsAddress() external returns (address) envfree;

    function helper_uint32ToBytes4(uint32 x) external  returns (bytes4) envfree;
    function helper_addressZero() external returns (address) envfree;
    function helper_maxUint256() external returns (uint256) envfree;
    function helper_recoverAddress(address owner, address spender, uint256 amount, uint256 deadline, uint8 v, bytes32 r, bytes32 s) external returns (address) envfree;

    function balanceOf(address) external returns (uint256) envfree;
    function totalSupply() external returns (uint256) envfree;
    function allowance(address, address) external returns (uint256) envfree;
    function nonces(address) external returns (uint256) envfree;
}

/* -------------------------------------------------------------------------- */
/*                                 INVARIANTS                                 */
/* -------------------------------------------------------------------------- */

ghost mathint sumAllBalances {
	init_state axiom sumAllBalances == 0; 
}

hook Sstore _balances[KEY address user] uint256 newBalance (uint256 oldBalance) STORAGE {
    sumAllBalances = sumAllBalances + newBalance - oldBalance;
}

/// @dev The sum of all balances should be equal to the total supply
invariant inv_totalBalancesEqualTotalSupply()
    sumAllBalances == to_mathint(totalSupply());

/* -------------------------------------------------------------------------- */
/*                                    RULES                                   */
/* -------------------------------------------------------------------------- */

use rule sanity;

/// @dev Getter functions should never revert
rule gettersNeverRevert(method f) {
    address a;
    address b;

    env e;
    require e.msg.value == 0;

    if (f.selector == sig:balanceOf(address).selector) {
      balanceOf@withrevert(e, a);
    } else if (f.selector == sig:allowance(address,address).selector) {
      allowance@withrevert(e, a, b);
    } else if (f.selector == sig:nonces(address).selector) {
      nonces@withrevert(e, a);
    } else {
      calldataarg args;
      f@withrevert(e, args);
    }

    assert (
        f.selector == sig:totalSupply().selector ||
        f.selector == sig:balanceOf(address).selector ||
        f.selector == sig:allowance(address,address).selector ||
        f.selector == sig:DOMAIN_SEPARATOR().selector ||
        f.selector == sig:domainSeparator().selector ||
        f.selector == sig:nonces(address).selector ||
        f.selector == sig:name().selector ||
        f.selector == sig:symbol().selector ||
        f.selector == sig:decimals().selector ||
        f.selector == sig:version().selector ||
        f.selector == sig:permitTypeHash().selector
    ) => !lastReverted;
}

/// @dev Change in EBTC Token balances should only occur in the following cases (when calling):
/// - mint
/// - burn
/// - transfer
/// - transferFrom
/// => In all other cases, the balances should never change
/// @dev Changes in EBTC Token total supply should only occur in the following cases (when calling):
/// - mint
/// - burn
/// => In all other cases, the total supply should never change
/// @dev Changes in EBTC Token approvals should only occur in the following cases (when calling):
/// - approve
/// - increaseAllowance
/// - decreaseAllowance
/// - transferFrom
/// - permit
/// => In all other cases, the approvals should never change
rule changesToBalanceAndTotalSupply(method f) {
  address account;
  uint256 balanceBefore = balanceOf(account);
  uint256 allowanceBefore = allowance(account, account);
  uint256 totalSupplyBefore = totalSupply();

  env e;
  calldataarg args;
  f(e, args);

  uint256 balanceAfter = balanceOf(account);
  uint256 allowanceAfter = allowance(account, account);
  uint256 totalSupplyAfter = totalSupply();

  assert balanceAfter != balanceBefore =>
    (
      f.selector == sig:mint(address,uint256).selector ||
      f.selector == sig:burn(address,uint256).selector ||
      f.selector == sig:burn(uint256).selector ||
      f.selector == sig:transfer(address,uint256).selector ||
      f.selector == sig:transferFrom(address,address,uint256).selector
    );

  assert totalSupplyAfter != totalSupplyBefore =>
    (
      f.selector == sig:mint(address,uint256).selector ||
      f.selector == sig:burn(address,uint256).selector ||
      f.selector == sig:burn(uint256).selector
    );

  assert allowanceAfter != allowanceBefore =>
    (
      f.selector == sig:approve(address,uint256).selector ||
      f.selector == sig:increaseAllowance(address,uint256).selector ||
      f.selector == sig:decreaseAllowance(address,uint256).selector ||
      f.selector == sig:transferFrom(address,address,uint256).selector ||
      f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector
    );
}

/// @dev Minting of tokens should only occur in the following conditions:
/// 1. When the function called is `mint`
/// 2. When the caller is authorized (see `call_isBOOrCdpMOrAuth`)
/// 3. When the target is not the zero address
/// => Both the balance of the target and the total supply should increase by the amount minted
/// => The balance of all other addresses should not change
rule mintTokens(method f) {
    address account;
    address user;
    uint256 amount;

    uint256 accountBalanceBefore = balanceOf(account);
    uint256 userBalanceBefore = balanceOf(user);
    uint256 totalSupplyBefore = totalSupply();

    env e;
    callMintWithParams(f, e, account, amount);

    uint256 accountBalanceAfter = balanceOf(account);
    uint256 userBalanceAfter = balanceOf(user);
    uint256 totalSupplyAfter = totalSupply();

    // Verify that if the balance of the account and totalSupply have increased
    // > The caller is authorized (see `call_isBOOrCdpMOrAuth`), the function called is mint and the target is not the zero address
    require amount > 0;
    assert (
        to_mathint(accountBalanceAfter) == accountBalanceBefore + amount &&
        to_mathint(totalSupplyAfter) == totalSupplyBefore + amount
    ) => (
        call_isBOOrCdpMOrAuth(e.msg.sender, helper_uint32ToBytes4(sig:mint(address,uint256).selector)) &&
        f.selector == sig:mint(address,uint256).selector &&
        account != helper_addressZero()
    );

    // The balances of other users should not have increased
    // Except if the function called is `burn`, `transfer` or `transferFrom`
    require user != account;
    if (
        f.selector == sig:burn(address,uint256).selector ||
        f.selector == sig:burn(uint256).selector ||
        f.selector == sig:transfer(address,uint256).selector ||
        f.selector == sig:transferFrom(address,address,uint256).selector
    ) {
        assert true; // we check these in other rules
    } else {
        assert userBalanceAfter == userBalanceBefore;
    }
}

/// @dev Burning of tokens should only occur in the following conditions:
/// 1. When the function called is `burn`
/// 2. When the caller is authorized (see `call_isBOOrCdpMOrAuth`)
/// 3. When the target is not the zero address
/// => Both the balance of the target and the total supply should decrease by the amount burned
/// => The balance of all other addresses should not change
/// @dev There are two `burn` functions:
/// 1. `burn(address,uint256)` => burns tokens from the target address
/// 2. `burn(uint256)` => burns tokens from the caller address
/// @dev Both perform virtually the same (only the target is either specified or the caller)
rule burnTokens(method f) {
    address account;
    address user;
    uint256 amount;

    uint256 accountBalanceBefore = balanceOf(account);
    uint256 userBalanceBefore = balanceOf(user);
    uint256 totalSupplyBefore = totalSupply();

    env e;
    callBurnWithParams(f, e, account, amount);

    uint256 accountBalanceAfter = balanceOf(account);
    uint256 userBalanceAfter = balanceOf(user);
    uint256 totalSupplyAfter = totalSupply();

    require amount > 0;
    // Verify that if the balance of the account and totalSupply have decreased
    // > The caller is authorized (see `call_isBOOrCdpMOrAuth`), the amount is <= to the balance, the function called is burn and the target is not the zero address (for the first burn function)
    assert (
        to_mathint(accountBalanceAfter) == accountBalanceBefore - amount &&
        to_mathint(totalSupplyAfter) == totalSupplyBefore - amount
    ) => (
        // Either:
        ((f.selector == sig:burn(address,uint256).selector && call_isBOOrCdpMOrAuth(e.msg.sender, helper_uint32ToBytes4(sig:burn(address,uint256).selector))) ||
        // Or:
        (f.selector == sig:burn(uint256).selector && call_isBOOrCdpMOrAuth(e.msg.sender, helper_uint32ToBytes4(sig:burn(uint256).selector)))) &&
        // And:
        amount <= accountBalanceBefore &&
        account != helper_addressZero()
    );

    // The balances of other users should not have decreased
    // Except if the function called is `mint`, `transfer` or `transferFrom`
    require user != account && user != e.msg.sender;
    if (
        f.selector == sig:mint(address,uint256).selector ||
        f.selector == sig:transfer(address,uint256).selector ||
        f.selector == sig:transferFrom(address,address,uint256).selector
    ) {
        assert true; // we check these in other rules
    } else {
        assert userBalanceAfter == userBalanceBefore;
    }
}

/// @dev Transfer of tokens should only occur in the following conditions:
/// 1. When the function called is `transfer` (also during `transferFrom` although but not in this rule)
/// 2. When the recipient is not a reserved address (zero address, EBTCToken contract, cdpManager or borrowerOperations)
/// 3. When the amount is <= to the balance of the caller
/// => The transfer should return true
/// => The balance of the caller should decrease by the amount transferred
/// => The balance of the recipient should increase by the amount transferred
/// => The balance of all other addresses should not change
rule transferTokens(method f) {
    address caller;
    address recipient;
    address user;
    uint256 amount;

    uint256 callerBalanceBefore = balanceOf(caller);
    uint256 recipientBalanceBefore = balanceOf(recipient);
    uint256 userBalanceBefore = balanceOf(user);

    bool success;
    env e;
    calldataarg args;

    // callTransferWithParams but we need the return value
    if (f.selector == sig:transfer(address,uint256).selector) {
        success = transfer(e, recipient, amount);
    } else {
        f(e, args);
        success = false;
    }

    uint256 callerBalanceAfter = balanceOf(caller);
    uint256 recipientBalanceAfter = balanceOf(recipient);
    uint256 userBalanceAfter = balanceOf(user);

    // Verify that if tokens are transferrer from a user to another
    // > The caller is the sender, the function called is `transfer` or `transferFrom`, the recipient is a valid address and the amount is not greater than their balance
    require amount > 0;
    require caller == e.msg.sender;
    require caller != recipient;
    assert (
        to_mathint(callerBalanceAfter) == callerBalanceBefore - amount &&
        to_mathint(recipientBalanceAfter) == recipientBalanceBefore + amount
    ) => (
        (f.selector == sig:transfer(address,uint256).selector || f.selector == sig:transferFrom(address,address,uint256).selector) &&
        call_isValidTransfer(caller, recipient) &&
        amount <= callerBalanceBefore &&
        // Assume that the transfer is successful if the function called is `transferFrom`
        // It has a dedicated rule anyway
        (success || f.selector == sig:transferFrom(address,address,uint256).selector)
    );

    // For all other addresses, the balance should not have changed
    require user != caller && user != recipient;
    if (
        f.selector == sig:mint(address,uint256).selector ||
        f.selector == sig:burn(address,uint256).selector ||
        f.selector == sig:burn(uint256).selector ||
        f.selector == sig:transferFrom(address,address,uint256).selector
    ) {
        assert true; // we check these in other rules
    } else {
        assert userBalanceBefore == userBalanceAfter;
    }
}

/// @dev Transfer of tokens should only occur in the following conditions:
/// 1. When the function called is `transferFrom` (also during `transfer` although but not in this rule)
/// 2. When the recipient is not a reserved address (zero address, EBTCToken contract, cdpManager or borrowerOperations)
/// 3. When the sender (owner) is not the zero address
/// 4. When the amount is <= to the balance of the caller
/// 5. When the amount is <= to the allowance of the sender for the caller
/// => The transfer should return true
/// => The balance of the sender should decrease by the amount transferred
/// => The balance of the recipient should increase by the amount transferred
/// => The balance of all other addresses should not change
/// IF the allowance is not unlimited (2^256 - 1)
/// => The allowance of the sender for the caller should decrease by the amount transferred
rule transferFromTokens(method f) {
    address sender;
    address caller;
    address recipient;
    address user;
    uint256 amount;

    uint256 senderBalanceBefore = balanceOf(sender);
    uint256 callerBalanceBefore = balanceOf(caller);
    uint256 recipientBalanceBefore = balanceOf(recipient);
    uint256 userBalanceBefore = balanceOf(user);
    uint256 allowanceBefore = allowance(sender, caller);
    uint256 userAllowanceBefore = allowance(user, caller);

    bool success;
    env e;
    calldataarg args;

    // callTransferFromWithParams but we need the return value
    if (f.selector == sig:transferFrom(address,address,uint256).selector) {
        success = transferFrom(e, sender, recipient, amount);
    } else {
        f(e, args);
        success = false;
    }

    uint256 senderBalanceAfter = balanceOf(sender);
    uint256 callerBalanceAfter = balanceOf(caller);
    uint256 recipientBalanceAfter = balanceOf(recipient);
    uint256 userBalanceAfter = balanceOf(user);
    uint256 allowanceAfter = allowance(sender, caller);
    uint256 userAllowanceAfter = allowance(user, caller);

    require amount > 0;
    require caller == e.msg.sender && sender != recipient;
    // Verify that if tokens are transferred from a user to another
    // > The function called is `transfer` or `transferFrom`, the sender is a valid address, the recipient is a valid address, the sender has enough balance and the spender has enough allowance
    assert (
        to_mathint(senderBalanceAfter) == senderBalanceBefore - amount &&
        to_mathint(recipientBalanceAfter) == recipientBalanceBefore + amount
    ) => (
        (f.selector == sig:transferFrom(address,address,uint256).selector || f.selector == sig:transfer(address,uint256).selector) &&
        call_isValidTransfer(sender, recipient) &&
        amount <= senderBalanceBefore &&
        // If it was `transfer`, allowance is not needed and success won't be set to true
        (amount <= allowanceBefore || f.selector == sig:transfer(address,uint256).selector) &&
        (success || f.selector == sig:transfer(address,uint256).selector)
    );

    // (Only when the allowance is not unlimited (2^256 - 1))
    // Verify that if the allowance of the sender for the caller has decreased
    // > An equivalent amount of tokens was indeed transferred from the sender to the recipient
    if (f.selector == sig:transferFrom(address,address,uint256).selector) {
        assert to_mathint(allowanceAfter) == allowanceBefore - amount => (
            to_mathint(senderBalanceAfter) == senderBalanceBefore - amount &&
            to_mathint(recipientBalanceAfter) == recipientBalanceBefore + amount
        );
    }

    // For all other addresses, the balance and allowance should not have changed
    require user != sender && user != recipient;
    if (f.selector != sig:transferFrom(address,address,uint256).selector) {
        assert true; // we check these in other rules
    } else {
        assert (
            userBalanceBefore == userBalanceAfter &&
            userAllowanceBefore == userAllowanceAfter
        );
    }
}

/// @dev Approval of tokens (increasing/decreasing allowance) should only occur in the following conditions:
/// 1. When the sender (owner) is not the zero address
/// 2. When the spender is not the zero address
/// If the function called is `decreaseAllowance` or `transferFrom`
///     3. When the amount is <= to the allowance of the caller for the spender
/// If the function called is `transferFrom`
///     4. When the allowance is not unlimited (2^256 - 1)
/// => The allowance of the caller for the spender should increase/decrease by the amount specified
/// => The allowance of all other addresses should not change
rule approveTokens(method f) {
    address caller;
    address spender;
    address user;
    uint256 amount;

    uint256 allowanceBefore = allowance(caller, spender);
    uint256 userAllowanceBefore = allowance(user, spender);
    mathint expectedAllowanceAfter;

    bool success;
    env e;
    calldataarg args;

    // call[...]WithParams but we need the return value
    if (f.selector == sig:approve(address,uint256).selector) {
        success = approve(e, spender, amount);
    } else if (f.selector == sig:increaseAllowance(address,uint256).selector) {
        success = increaseAllowance(e, spender, amount);
    } else if (f.selector == sig:decreaseAllowance(address,uint256).selector) {
        success = decreaseAllowance(e, spender, amount);
    } else if (f.selector == sig:transferFrom(address,address,uint256).selector) {
        success = transferFrom(e, caller, user, amount); // we don't care about the recipient
    } else if (f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector) {
      // permit is a special case, we will test it in another rule
      success = false;
    } else {
        f(e, args);
        success = false;
    }

    uint256 allowanceAfter = allowance(caller, spender);
    uint256 userAllowanceAfter = allowance(user, spender);

    require amount > 0;
    require caller == e.msg.sender;
    // Verify that if the allowance of the caller for the spender has increased
    // > The function called is `approve` or `increaseAllowance`, the spender is a valid address
    assert to_mathint(allowanceAfter) == allowanceBefore + amount => (
        (f.selector == sig:approve(address,uint256).selector || f.selector == sig:increaseAllowance(address,uint256).selector) &&
        spender != helper_addressZero() &&
        success
    );

    // Verify that if the allowance of the caller for the spender has decreased
    // > The function called is `approve`, `decreaseAllowance` or `transferFrom`, the spender is a valid address, the amount is <= to the allowance of the caller for the spender
    assert to_mathint(allowanceAfter) == allowanceBefore - amount => (
        (
            f.selector == sig:approve(address,uint256).selector ||
            f.selector == sig:decreaseAllowance(address,uint256).selector ||
            f.selector == sig:transferFrom(address,address,uint256).selector
        ) && spender != helper_addressZero() && amount <= allowanceBefore && success
    );

    // For all other addresses, the allowance should not have changed
    require user != caller;
    assert userAllowanceBefore == userAllowanceAfter;
}

/// @dev Approval through `permit` should only occur in the following conditions:
/// 1. When the deadline is not passed (deadline < block.timestamp)
/// 2. When the recovered address is indeed the owner
/// => The allowance of the owner for the spender should be set to the amount specified
rule permitTokens(method f) {
    address owner;
    address spender;
    address user;
    uint256 amount;
    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;

    uint256 nonceBefore = nonces(owner);
    uint256 userAllowanceBefore = allowance(user, spender);
    uint256 userNonceBefore = nonces(user);

    env e;
    calldataarg args;
    if (f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector) {
        permit(e, owner, spender, amount, deadline, v, r, s);
    } else {
        f(e, args);
    }

    uint256 allowanceAfter = allowance(owner, spender);
    uint256 nonceAfter = nonces(owner);
    uint256 userAllowanceAfter = allowance(user, spender);
    uint256 userNonceAfter = nonces(user);

    // Verify that if the allowance was updated and the function called is `permit`
    // > The deadline is not passed, the recovered address is indeed the owner of the tokens, and the nonce for the owner has increased
    assert (allowanceAfter == amount && f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector) => (
        deadline >= e.block.timestamp && 
        helper_recoverAddress(owner, spender, amount, deadline, v, r, s) == owner &&
        to_mathint(nonceAfter) == nonceBefore + 1
    );

    // For all other addresses, the allowance and nonces should not have changed
    require user != owner;
    if (f.selector == sig:approve(address,uint256).selector ||
        f.selector == sig:increaseAllowance(address,uint256).selector ||
        f.selector == sig:decreaseAllowance(address,uint256).selector ||
        f.selector == sig:transferFrom(address,address,uint256).selector
    ) {
        assert true; // we check these in other rules
    } else {
        assert userAllowanceBefore == userAllowanceAfter;
    }

    require user != e.msg.sender;
    assert userNonceBefore == userNonceAfter;
}

/* -------------------------------------------------------------------------- */
/*                                   HELPERS                                  */
/* -------------------------------------------------------------------------- */

/// @dev Helper function to call `mint` with the correct parameters IF this is the function being called
/// @dev If not, it will call the function with calldataarg
function callMintWithParams(method f, env e, address account, uint256 amount) {
    if (f.selector == sig:mint(address,uint256).selector) {
        mint(e, account, amount);
    } else {
        calldataarg args;
        f(e, args);
    }
}

/// @dev Helper function to call `burn` with the correct parameters IF this is the function being called
/// @dev If not, it will call the function with calldataarg
function callBurnWithParams(method f, env e, address account, uint256 amount) {
    if (f.selector == sig:burn(address,uint256).selector) {
        burn(e, account, amount);
    } else if (f.selector == sig:burn(uint256).selector) {
        burn(e, amount);
    } else {
        calldataarg args;
        f(e, args);
    }
}