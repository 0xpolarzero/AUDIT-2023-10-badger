import "./sanity.spec";
import "./erc20.spec";

/// @dev Verify on original (harness) contract:
/// certoraRun certora/confs/ActivePool_verified.conf
/// @dev Verify against mutations:
/// certoraMutate --prover_conf certora/confs/ActivePool_verified.conf --mutation_conf certora/confs/gambit/ActivePool.conf

using CollateralTokenTester as collateral;

/* -------------------------------------------------------------------------- */
/*                                   METHODS                                  */
/* -------------------------------------------------------------------------- */

methods {
   // Helper functions
    function call_isAuthorized(address user, bytes4 functionSig) external returns (bool) envfree;
    function helper_uint32ToBytes4(uint32) external returns (bytes4) envfree;
    function helper_calculateFeeAllocatedToFeeRecipientAfterSync() external returns (uint256) envfree;

    // ActivePool public getters
    function borrowerOperationsAddress() external returns (address) envfree;
    function feeRecipientAddress() external returns (address) envfree;
    function cdpManagerAddress() external returns (address) envfree;
    function collSurplusPoolAddress() external returns (address) envfree;

    // ActivePool external getters
    function getSystemCollShares() external returns (uint256) envfree;
    function getSystemDebt() external returns (uint256) envfree;
    function getFeeRecipientClaimableCollShares() external returns (uint256) envfree;

    // ActivePool methods
    function increaseSystemCollShares(uint256) external;
    function transferSystemCollSharesAndLiquidatorReward(address, uint256, uint256) external;
     
     // Collateral methods
    function collateral.balanceOf(address) external returns (uint256) envfree;
    function collateral.sharesOf(address) external returns (uint256) envfree;
    function collateral.getPooledEthByShares(uint256) external returns (uint256) envfree;

    // ERC3156 FlashLender
    function _.increaseTotalSurplusCollShares(uint256) external => DISPATCHER(true);
    function _.onFlashLoan(address, address, uint256, uint256, bytes) external => DISPATCHER(true);

    // External calls to collateral contract
    // function _.sharesOf(address) external => DISPATCHER(true);

}

/* -------------------------------------------------------------------------- */
/*                                 INVARIANTS                                 */
/* -------------------------------------------------------------------------- */

/* ----------------------------- GHOST VARIABLES ---------------------------- */
/// @dev Init ghost for `systemCollShares` from the ActivePool contract
ghost mathint mirror_systemCollShares {
	  init_state axiom mirror_systemCollShares == 0; 
}

/// @dev Init ghost for `feeRecipientClaimableCollShares` from the ActivePool contract
ghost mathint mirror_feeRecipientClaimableCollShares {
    init_state axiom mirror_feeRecipientClaimableCollShares == 0; 
}

/// @dev Init ghost for `sharesOf()` from the collateral contract
ghost mapping(address => mathint) mirror_sharesOf {
    init_state axiom forall address a. mirror_sharesOf[a] == 0;
}

/* ---------------------------------- HOOKS --------------------------------- */
/// @dev Enfore `mirror_systemCollShares` to be equal to value read from storage
hook Sload uint256 newCollShares systemCollShares STORAGE {
  require mirror_systemCollShares == to_mathint(newCollShares);
}

/// @dev Enfore `mirror_feeRecipientClaimableCollShares` to be equal to value read from storage 
hook Sload uint256 newCollShares feeRecipientCollShares STORAGE {
  require mirror_feeRecipientClaimableCollShares == to_mathint(newCollShares);
}

/// @dev Enfore `mirror_sharesOf` to be equal to value read from storage
hook Sload uint256 newCollShares collateral.balances[KEY address a]/* .(offset 0) */ STORAGE {
  require mirror_sharesOf[a] == to_mathint(newCollShares);
}

/// @dev Mirror updates to `systemCollShares` in `mirror_systemCollShares`
hook Sstore systemCollShares uint256 newCollShares (uint256 oldCollShares) STORAGE {
    mirror_systemCollShares = mirror_systemCollShares + (newCollShares - oldCollShares);
    // havoc mirror_systemCollShares assuming mirror_systemCollShares@new == mirror_systemCollShares@old + newCollShares - oldCollShares;
    // mirror_systemCollShares = newCollShares;
}

/// @dev Mirror updates to `feeRecipientClaimableCollShares` in `mirror_feeRecipientClaimableCollShares`
hook Sstore feeRecipientCollShares uint256 newCollShares (uint256 oldCollShares) STORAGE {
    mirror_feeRecipientClaimableCollShares = mirror_feeRecipientClaimableCollShares + (newCollShares - oldCollShares);
    // havoc mirror_feeRecipientClaimableCollShares assuming mirror_feeRecipientClaimableCollShares@new == mirror_feeRecipientClaimableCollShares@old + newCollShares - oldCollShares;
}

/// @dev Mirror updates to `collateral.sharesOf()` (tracked in a `balances` mapping) in `mirror_sharesOf`
hook Sstore collateral.balances[KEY address a] uint256 newCollShares (uint256 oldCollShares) STORAGE {
    mirror_sharesOf[a] = mirror_sharesOf[a] + (newCollShares - oldCollShares);
}

/// @dev Shares reported by the collateral contract for ActivePool 
/// should always be >= to the tracked shares for both the system and the fee recipient
/// It could be greater since anyone can send tokens to the contract, but it should never be less
invariant inv_trackedCollSharesAlwaysGreaterOrEqualBalance()
    mirror_sharesOf[currentContract] >= mirror_systemCollShares + mirror_feeRecipientClaimableCollShares
        filtered {
            // Actually, we need to rule out the following case, that artificially increases the collateral shares
            f -> f.selector != sig:increaseSystemCollShares(uint256).selector
        } {
            // And rectify the shares tracked for the system
            preserved transferSystemCollSharesAndLiquidatorReward(address _account, uint256 _shares, uint256 liquidatorRewardShares) with (env _e) {
                // In the contract, `systemCollShares` is decreased by `shares`
                // However, it transfers out `shares + liquidatorRewardShares`,
                // so we need to account for the liquidator reward here
                mirror_systemCollShares = mirror_systemCollShares - liquidatorRewardShares;
            }
        }

/* -------------------------------------------------------------------------- */
/*                                    RULES                                   */
/* -------------------------------------------------------------------------- */

use rule sanity;

/// @dev Getter functions should never revert
rule gettersNeverRevert(method f) {
    address a;

    env e;
    calldataarg args;
    require e.msg.value == 0;
    f@withrevert(e, args);

    assert (
        f.selector == sig:getSystemCollShares().selector ||
        f.selector == sig:getSystemDebt().selector ||
        f.selector == sig:getFeeRecipientClaimableCollShares().selector
    ) => !lastReverted;
}

/// @dev Change to the collateral shares should only occur in such ways:
/// 1. `systemCollShares` increased
///     - The borrower operations called `increaseSystemCollShares`
///         => The system collateral shares are increased by the specified amount
/// 2. `systemCollShares` decreased
///     - The borrower operations or cdp manager called `transferSystemCollShares`
///         => The system collateral shares are decreased by the specified amount
///         => The shares are transferred to the specified account
///     - The borrower operations or cdp manager called `transferSystemCollSharesAndLiquidatorReward`
///         => The system collateral shares are decreased by the specified amount
///         => The shares + specified liquidator reward are transferred to the specified account
///     - The cdp manager called `allocateSystemCollSharesToFeeRecipient`
///         => The system collateral shares are decreased by the specified amount
///         => The fee recipient collateral shares are increased by the specified amount
rule changeToCollSharesTracker(method f) {
    address account;
    address user;
    uint256 amount;
    uint256 liquidatorReward;

    uint256 systemCollSharesBefore = getSystemCollShares();
    uint256 feeRecipientCollSharesBefore = getFeeRecipientClaimableCollShares();
    uint256 collSharesBalanceBeforeContract = collateral.sharesOf(currentContract);
    uint256 collSharesBalanceBeforeAccount = collateral.sharesOf(account);
    uint256 collSharesBalanceBeforeUser = collateral.sharesOf(user);

    env e;
    callCollSharesFunctionWithParams(f, e, account, amount, liquidatorReward);

    uint256 systemCollSharesAfter = getSystemCollShares();
    uint256 feeRecipientCollSharesAfter = getFeeRecipientClaimableCollShares();
    uint256 collSharesBalanceAfterContract = collateral.sharesOf(currentContract);
    uint256 collSharesBalanceAfterAccount = collateral.sharesOf(account);
    uint256 collSharesBalanceAfterUser = collateral.sharesOf(user);

    uint256 expectedSystemCollSharesAfter = systemCollSharesBefore;
    uint256 expectedFeeRecipientCollSharesAfter = feeRecipientCollSharesBefore;
    uint256 expectedCollSharesBalanceAfterContract = collSharesBalanceBeforeContract;
    uint256 expectedCollSharesBalanceAfterAccount = collSharesBalanceBeforeAccount;

    // There is a special case where a function makes a call to `ICdpManagerData(cdpManagerAddress).syncGlobalAccountingAndGracePeriod()`.
    // which calculates a new fee allocated to the fee recipient.
    if (f.selector == sig:increaseSystemCollShares(uint256).selector) {
      expectedSystemCollSharesAfter = systemCollSharesBefore + amount;
    } else if (f.selector == sig:transferSystemCollShares(address,uint256).selector) {
      expectedSystemCollSharesAfter = systemCollSharesBefore + amount;
      expectedCollSharesBalanceAfterAccount = collSharesBalanceBeforeAccount + amount;
      expectedCollSharesBalanceAfterContract = collSharesBalanceBeforeContract - amount;
    } else if (f.selector == sig:transferSystemCollSharesAndLiquidatorReward(address,uint256,uint256).selector) {
      expectedSystemCollSharesAfter = systemCollSharesBefore + amount;
      expectedCollSharesBalanceAfterAccount = collSharesBalanceBeforeAccount + amount + liquidatorReward;
      expectedCollSharesBalanceAfterContract = collSharesBalanceBeforeContract - amount - liquidatorReward;
    } else if (f.selector == sig:allocateSystemCollSharesToFeeRecipient(uint256).selector) {
      expectedSystemCollSharesAfter = systemCollSharesBefore - amount;
      expectedFeeRecipientCollSharesAfter = feeRecipientCollSharesBefore + amount;
    // Special case where the call to `ICdpManagerData(cdpManagerAddress).syncGlobalAccountingAndGracePeriod()` is made
    } else if (
        f.selector == sig:claimFeeRecipientCollShares(uint256).selector ||
        f.selector == sig:increaseSystemCollShares(uint256).selector ||
        f.selector == sig:setFeeBps(uint256).selector ||
        f.selector == sig:setFeeRecipientAddress(address).selector ||
        f.selector == sig:setFlashLoansPaused(bool).selector ||
        f.selector == sig:sweepToken(address,uint256).selector
    ) {
      uint256 newAllocatedFee = helper_calculateFeeAllocatedToFeeRecipientAfterSync();
      expectedFeeRecipientCollSharesAfter = feeRecipientCollSharesBefore + newAllocatedFee;
      expectedSystemCollSharesAfter = systemCollSharesBefore - newAllocatedFee;
    }
    
    require account != currentContract && account != feeRecipientAddress();
    // Verify that if there is an increase in system collateral shares
    // > The caller is the borrower operations contract and the function is `increaseSystemCollShares`
    assert systemCollSharesAfter > systemCollSharesBefore => (
        // f.selector == sig:increaseSystemCollShares(uint256).selector &&
        e.msg.sender == borrowerOperationsAddress() &&
        // to_mathint(systemCollSharesAfter) == systemCollSharesBefore + amount
    );

    // Verify that if there is a decrease in system collateral shares
    // > See inline comments
    assert systemCollSharesAfter < systemCollSharesBefore => (
        // > The function is `transferSystemCollShares`, `transferSystemCollSharesAndLiquidatorReward` or `allocateSystemCollSharesToFeeRecipient`
        (
            f.selector == sig:transferSystemCollShares(address,uint256).selector || 
            f.selector == sig:transferSystemCollSharesAndLiquidatorReward(address,uint256,uint256).selector || 
            f.selector == sig:allocateSystemCollSharesToFeeRecipient(uint256).selector
        // > The caller is the borrower operations contract or the cdp manager
        ) && (e.msg.sender == borrowerOperationsAddress() || e.msg.sender == cdpManagerAddress()) &&
        // > There was enough tracked collateral shares
        systemCollSharesBefore >= amount &&
        // > The system collateral shares are decreased by the specified amount
        // to_mathint(systemCollSharesAfter) == systemCollSharesBefore - amount
    );

    // If the function is `transferSystemCollShares`
    assert f.selector == sig:transferSystemCollShares(address,uint256).selector => (
        // > The shares are transferred to the specified account
        to_mathint(collSharesBalanceAfterAccount) == collSharesBalanceBeforeAccount + amount &&
        to_mathint(collSharesBalanceAfterContract) == collSharesBalanceBeforeContract - amount
    );
    // If the function is `transferSystemCollSharesAndLiquidatorReward`
    assert f.selector == sig:transferSystemCollSharesAndLiquidatorReward(address,uint256,uint256).selector => (
        // > The shares + specified liquidator reward are transferred to the specified account
        to_mathint(collSharesBalanceAfterAccount) == collSharesBalanceBeforeAccount + amount + liquidatorReward &&
        to_mathint(collSharesBalanceAfterContract) == collSharesBalanceBeforeContract - amount - liquidatorReward
    );
    // If the function is `allocateSystemCollSharesToFeeRecipient`
    assert f.selector == sig:allocateSystemCollSharesToFeeRecipient(uint256).selector => (
        // > The caller is the cdp manager
        e.msg.sender == cdpManagerAddress() &&
        // > The fee recipient collateral shares are increased by the specified amount
        to_mathint(feeRecipientCollSharesAfter) == feeRecipientCollSharesBefore + amount
    );

    // Balances should not change for other users
    require user != account && user != currentContract && user != feeRecipientAddress();
    assert collSharesBalanceAfterUser == collSharesBalanceBeforeUser;
}

/// @dev Change to `systemDebt` should only occur in such ways:
/// 1. `systemDebt` increased
///     - The borrower operations or cdp manager called `increaseSystemDebt`
///         => The system debt is increased by the specified amount
/// 2. `systemDebt` decreased
///     - The borrower operations or cdp manager called `decreaseSystemDebt`
///         => The system debt is decreased by the specified amount
rule changeToSystemDebtTracker(method f) {
    uint256 amount;
    uint256 systemDebtBefore = getSystemDebt();

    env e;
    callSystemDebtFunctionWithParams(f, e, amount);

    uint256 systemDebtAfter = getSystemDebt();

    // Verify that if there is a difference in system debt
    // > The caller is the borrower operations contract or the cdp manager and the function is `increaseSystemDebt` or `decreaseSystemDebt`
    assert systemDebtAfter != systemDebtBefore => (
        (
            // > Either the function is `increaseSystemDebt` => The system debt is increased by the specified amount
            (f.selector == sig:increaseSystemDebt(uint256).selector && to_mathint(systemDebtAfter) == systemDebtBefore + amount) ||
            // > Or the function is `decreaseSystemDebt` => The system debt is decreased by the specified amount
            (f.selector == sig:decreaseSystemDebt(uint256).selector && to_mathint(systemDebtAfter) == systemDebtBefore - amount)
        ) && (e.msg.sender == borrowerOperationsAddress() || e.msg.sender == cdpManagerAddress())
    );
}

/// @dev Change to `feeRecipientClaimableCollShares` should only occur in such ways:
/// 1. `feeRecipientClaimableCollShares` increased
///     - The borrower operations or cdp manager called `allocateSystemCollSharesToFeeRecipient`
///         => The fee recipient claimable collateral shares are increased by the specified amount
/// 2. `feeRecipientClaimableCollShares` decreased
///     - An authorized entity called `claimFeeRecipientCollShares`
///         => The function `CpdManagerData.syncGlobalAccountingAndGracePeriod()` is called
///         => The fee recipient claimable collateral shares are decreased by the specified amount
///         => The shares are transferred to the fee recipient
rule changeToFeeRecipientCollSharesTracker(method f) {
    address user;
    uint256 amount;
    uint256 feeRecipientCollSharesBefore = getFeeRecipientClaimableCollShares();
    uint256 collSharesBalanceBeforeFeeRecipient = collateral.sharesOf(feeRecipientAddress());
    uint256 collSharesBalanceBeforeContract = collateral.sharesOf(currentContract);
    uint256 collSharesBalanceBeforeUser = collateral.sharesOf(user);

    env e;
    callFeeRecipientCollSharesFunctionWithParams(f, e, amount);

    uint256 feeRecipientCollSharesAfter = getFeeRecipientClaimableCollShares();
    uint256 collSharesBalanceAfterFeeRecipient = collateral.sharesOf(feeRecipientAddress());
    uint256 collSharesBalanceAfterContract = collateral.sharesOf(currentContract);
    uint256 collSharesBalanceAfterUser = collateral.sharesOf(user);

    // Verify that if the fee recipient claimable collateral shares increased
    // > The caller is the cdp manager and the function is `allocateSystemCollSharesToFeeRecipient`
    assert feeRecipientCollSharesAfter > feeRecipientCollSharesBefore => (
        f.selector == sig:allocateSystemCollSharesToFeeRecipient(uint256).selector &&
        e.msg.sender == cdpManagerAddress() &&
        to_mathint(feeRecipientCollSharesAfter) == feeRecipientCollSharesBefore + amount
    );

    // Verify that if the fee recipient claimable collateral shares decreased
    // > The caller is authorized and the function is `claimFeeRecipientCollShares`
    assert feeRecipientCollSharesAfter < feeRecipientCollSharesBefore => (
        f.selector == sig:claimFeeRecipientCollShares(uint256).selector &&
        call_isAuthorized(e.msg.sender, helper_uint32ToBytes4(sig:claimFeeRecipientCollShares(uint256).selector)) &&
        feeRecipientCollSharesBefore >= amount &&
        to_mathint(feeRecipientCollSharesAfter) == feeRecipientCollSharesBefore - amount &&
        // > The shares are transferred to the fee recipient
        to_mathint(collSharesBalanceAfterFeeRecipient) == collSharesBalanceBeforeFeeRecipient + amount &&
        to_mathint(collSharesBalanceAfterContract) == collSharesBalanceBeforeContract - amount
    );

    // Balances should not change for other users
    require user != feeRecipientAddress() && user != currentContract;
    assert collSharesBalanceAfterUser == collSharesBalanceBeforeUser;
}

/* -------------------------------------------------------------------------- */
/*                                   HELPERS                                  */
/* -------------------------------------------------------------------------- */

/// @dev Helper function to call either `increaseSystemCollShares`, `transferSystemCollShares`, `transferSystemCollSharesAndLiquidatorReward` or `allocateSystemCollSharesToFeeRecipient`
/// with the correct parameters IF this is the function being called
/// @dev If not, it will call the function with calldataarg
function callCollSharesFunctionWithParams(method f, env e, address account, uint256 amount, uint256 liquidatorReward) {
    if (f.selector == sig:increaseSystemCollShares(uint256).selector) {
        increaseSystemCollShares(e, amount);
    } else if (f.selector == sig:transferSystemCollShares(address,uint256).selector) {
        transferSystemCollShares(e, account, amount);
    } else if (f.selector == sig:transferSystemCollSharesAndLiquidatorReward(address,uint256,uint256).selector) {
        transferSystemCollSharesAndLiquidatorReward(e, account, amount, liquidatorReward);
    } else if (f.selector == sig:allocateSystemCollSharesToFeeRecipient(uint256).selector) {
        allocateSystemCollSharesToFeeRecipient(e, amount);
    } else {
        calldataarg args;
        f(e, args);
    }
}

/// @dev Helper function to call either `increaseSystemDebt` or `decreaseSystemDebt`
/// with the correct parameters IF this is the function being called
function callSystemDebtFunctionWithParams(method f, env e, uint256 amount) {
    if (f.selector == sig:increaseSystemDebt(uint256).selector) {
        increaseSystemDebt(e, amount);
    } else if (f.selector == sig:decreaseSystemDebt(uint256).selector) {
        decreaseSystemDebt(e, amount);
    } else {
        calldataarg args;
        f(e, args);
    }
}

/// @dev Helper function to call either `allocateSystemCollSharesToFeeRecipient` or `claimFeeRecipientCollShares`
/// with the correct parameters IF this is the function being called
function callFeeRecipientCollSharesFunctionWithParams(method f, env e, uint256 amount) {
    if (f.selector == sig:allocateSystemCollSharesToFeeRecipient(uint256).selector) {
        allocateSystemCollSharesToFeeRecipient(e, amount);
    } else if (f.selector == sig:claimFeeRecipientCollShares(uint256).selector) {
        claimFeeRecipientCollShares(e, amount);
    } else {
        calldataarg args;
        f(e, args);
    }
}