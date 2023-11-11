import "./sanity.spec";
import "./erc20.spec";

/// @dev Verify on original (harness) contract:
/// certoraRun certora/confs/CollSurplusPool_verified.conf
/// @dev Verify against mutations:
/// certoraMutate --prover_conf certora/confs/CollSurplusPool_verified.conf --mutation_conf certora/confs/gambit/CollSurplusPool.conf

/// @dev Here we cover all possible balances updates, basically in this way:
/// If x kind of balance increased/decreased at any point, 
/// => it implies that a y specific set of interactions happened & the transfer happened in z specific way
/// @dev It includes balances in shares surplus, in collateral shares and in any arbitrary token...
/// ... modifications for an account, other users and special addresses (contract, feeRecipient).

using CollateralTokenTester as collateral;

/* -------------------------------------------------------------------------- */
/*                                   METHODS                                  */
/* -------------------------------------------------------------------------- */

methods {
    // Helper functions
    function call_isAuthorized(address user, bytes4 functionSig) external returns (bool) envfree;
    function helper_getTokenBalance(address token, address target) external returns (uint256) envfree;
    function helper_uint32ToBytes4(uint32 x) external returns (bytes4) envfree;

    // CollSurplusPool public getters
    function borrowerOperationsAddress() external returns (address) envfree;
    function feeRecipientAddress() external returns (address) envfree;
    function cdpManagerAddress() external returns (address) envfree;
    function activePoolAddress() external returns (address) envfree;
    // CollSurplusPool external getters
    function getTotalSurplusCollShares() external returns (uint256) envfree;
    function getSurplusCollShares(address _account) external returns (uint256) envfree;

    // CollSurplusPool methods
    function sweepToken(address token, uint256 amount) external;

    // Collateral methods
    function collateral.balanceOf(address) external returns (uint256) envfree;
    function collateral.sharesOf(address) external returns (uint256) envfree;
}

/* -------------------------------------------------------------------------- */
/*                                 INVARIANTS                                 */
/* -------------------------------------------------------------------------- */

ghost mathint sumSurplusCollShares {
	  init_state axiom sumSurplusCollShares == 0; 
}

hook Sstore balances[KEY address user] uint256 newBalance (uint256 oldBalance) STORAGE {
    sumSurplusCollShares = sumSurplusCollShares + newBalance - oldBalance;
}

/* -------------------------------------------------------------------------- */
/*                                    RULES                                   */
/* -------------------------------------------------------------------------- */

use rule sanity;

/// @dev Change to the collateral or surplus balances should only occur in such ways:
/// 1. The balance of the contract decreased
/// OR (the implications are identical)
/// 2. The balance of an account increased
/// OR
/// 3. The total surplus collateral shares decreased
/// OR
/// 4. The surplus collateral shares of an account decreased
///    - A user claimed their surplus
///       => The function called is `claimSurplusCollShares`
///       => The caller is the borrowerOperations
///       => The account has a non-zero balance (surplus)
///       => The total surplus collateral is >= the account's surplus
///       => The balance of the contract is decreased by the account's surplus
///       => The total surplus collateral shares is decreased by the account's surplus
///       => The account's surplus is decreased to 0
///       => The collateral is transferred from the contract to the account
rule changeToBalancesAfterClaim(method f) {
    address account;
    address user;
    uint256 amount;
    uint256 balanceBeforeAccount = collateral.sharesOf(account);
    uint256 balanceBeforeUser = collateral.sharesOf(user);
    uint256 balanceBeforeContract = collateral.sharesOf(currentContract);

    uint256 totalSurplusBefore = getTotalSurplusCollShares();
    uint256 surplusBeforeAccount = getSurplusCollShares(account);
    uint256 surplusBeforeUser = getSurplusCollShares(user);

    env e;
    callCollFunctionWithParams(f, e, account, amount);

    uint256 balanceAfterAccount = collateral.sharesOf(account);
    uint256 balanceAfterUser = collateral.sharesOf(user);
    uint256 balanceAfterContract = collateral.sharesOf(currentContract);

    uint256 totalSurplusAfter = getTotalSurplusCollShares();
    uint256 surplusAfterAccount = getSurplusCollShares(account);
    uint256 surplusAfterUser = getSurplusCollShares(user);

    require account != currentContract;
    // Verify that in any of the cases (see description above)
    // > An account has just claimed their surplus (see inline comments)
    assert (
        balanceAfterContract < balanceBeforeContract ||
        balanceAfterAccount > balanceBeforeAccount ||
        totalSurplusAfter < totalSurplusBefore ||
        surplusAfterAccount < surplusBeforeAccount
    ) => (
        // function called is `claimSurplusCollShares`
        f.selector == sig:claimSurplusCollShares(address).selector && 
        // caller is borrowerOperations
        e.msg.sender == borrowerOperationsAddress() &&
        // surplus was greater than 0
        surplusBeforeAccount > 0 &&
        // total surplus shares was greater than the amount attempted to be claimed
        totalSurplusBefore >= surplusBeforeAccount &&
        // surplus is reset to 0
        surplusAfterAccount == 0 &&
        // total surplus shares is reduced by the amount claimed
        to_mathint(totalSurplusAfter) == totalSurplusBefore - surplusBeforeAccount &&
        // user's balance is increased by the amount claimed
        to_mathint(balanceAfterAccount) == balanceBeforeAccount + surplusBeforeAccount &&
        // contract's balance is reduced by the amount claimed
        to_mathint(balanceAfterContract) == balanceBeforeContract - surplusBeforeAccount
    );

    // Verify that the surplus and balances of other accounts do not change
    require user != currentContract && user != account;
    assert (balanceAfterUser == balanceBeforeUser && surplusAfterUser == surplusBeforeUser);
}

/// @dev Change to the collateral or surplus balances should only occur in such ways:
/// 5. The total surplus collateral shares increased
///     - The activePool called `increaseTotalSurplusCollShares`
///         => The total surplus collateral shares is increased by the specified amount
/// 6. The surplus collateral shares of an account increased
///     - The cdpManager called `increaseSurplusCollShares`
///         => The surplus collateral shares of the caller is increased by the specified amount
/// 7. The shares of the contract increased
/// OR
/// 8. The shares of an account decreased
///    - This should never happen in the case of the provided functions in the contract
rule changeToBalancesSpecialCases(method f) {
    address account;
    address user;
    uint256 amount;
    uint256 balanceBeforeAccount = collateral.sharesOf(account);
    uint256 balanceBeforeContract = collateral.sharesOf(currentContract);
    uint256 totalSurplusBefore = getTotalSurplusCollShares();
    uint256 surplusBeforeAccount = getSurplusCollShares(account);

    env e;
    callCollFunctionWithParams(f, e, account, amount);

    uint256 balanceAfterAccount = collateral.sharesOf(account);
    uint256 balanceAfterContract = collateral.sharesOf(currentContract);
    uint256 totalSurplusAfter = getTotalSurplusCollShares();
    uint256 surplusAfterAccount = getSurplusCollShares(account);

    require account != currentContract;
    // Verify that in any case the shares of the contract cannot increase and the shares of an account cannot decrease
    assert (balanceAfterContract <= balanceBeforeContract && balanceAfterAccount >= balanceBeforeAccount);

    // Verify that if the total surplus collateral shares increased
    // > The activePool called `increaseTotalSurplusCollShares` and it increased by the specified amount
    assert (totalSurplusAfter > totalSurplusBefore) => (
        f.selector == sig:increaseTotalSurplusCollShares(uint256).selector &&
        e.msg.sender == activePoolAddress() &&
        to_mathint(totalSurplusAfter) == totalSurplusBefore + amount
    );

    // Verify that if the surplus collateral shares of an account increased
    // > The cdpManager called `increaseSurplusCollShares` and it increased by the specified amount
    assert (surplusAfterAccount > surplusBeforeAccount) => (
        f.selector == sig:increaseSurplusCollShares(address,uint256).selector &&
        e.msg.sender == cdpManagerAddress() &&
        to_mathint(surplusAfterAccount) == surplusBeforeAccount + amount
    );
}

/// @dev "Sweeping" of arbitrary tokens from the contract should only occur in the following conditions:
/// 1. The caller is authorized (see `call_isAuthorized`)
/// 2. The function called is `sweepToken`
/// 3. The token being swept is NOT the collateral token
/// 4. The amount being swept is less than or equal to the current balance of the contract
/// => The amount of the token should be transferred from the contract to the feeRecipient
/// @dev Any "sweeping" of tokens from the contract should only occur in the following conditions:
rule sweepOfArbitraryToken(method f) {
    address user;
    address token;
    uint256 amount;
    uint256 beforeContract = helper_getTokenBalance(token, currentContract);
    uint256 beforeRecipient = helper_getTokenBalance(token, feeRecipientAddress());
    uint256 beforeUser = helper_getTokenBalance(token, user);
    uint256 beforeSurplusUser = getSurplusCollShares(user);

    env e;
    callSweepTokenWithParams(f, e, token, amount);

    uint256 afterContract = helper_getTokenBalance(token, currentContract);
    uint256 afterRecipient = helper_getTokenBalance(token, feeRecipientAddress());
    uint256 afterUser = helper_getTokenBalance(token, user);
    uint256 afterSurplusUser = getSurplusCollShares(user);

    require token != collateral;
    require user != currentContract && user != feeRecipientAddress();
    // Verify that in any case there is:
    assert (
        // no internal way to increase the balance of the contract
        afterContract <= beforeContract &&
        //  or decrease the balance of the feeRecipient
        afterRecipient >= beforeRecipient &&
        //  or modify the balance of an account
        afterUser == beforeUser
    );

    require amount > 0;
    // Verify that either if tokens are being swept from the contract or sent to the feeRecipient
    // > The caller is authorized, the function called is `sweepToken`, the token being swept is not the collateral, and the contract has enough balance
    assert (afterContract < beforeContract || afterRecipient > beforeRecipient) => (
        f.selector == sig:sweepToken(address,uint256).selector && 
        call_isAuthorized(e.msg.sender, helper_uint32ToBytes4(sig:sweepToken(address,uint256).selector)) && 
        to_mathint(amount) <= to_mathint(beforeContract) &&
        // actual transfer of tokens
        to_mathint(afterContract) == beforeContract - amount &&
        to_mathint(afterRecipient) == beforeRecipient + amount &&
        // no other balances change
        afterUser == beforeUser &&
        afterSurplusUser == beforeSurplusUser
    );
}

/* -------------------------------------------------------------------------- */
/*                                   HELPERS                                  */
/* -------------------------------------------------------------------------- */

/// @dev Helper function to call either `increaseSurplusCollShares`, `claimSurplusCollShares` or `increaseTotalSurplusCollShares`
/// with the correct parameters IF this is the function being called
/// @dev If not, it will call the function with calldataarg
function callCollFunctionWithParams(method f, env e, address account, uint256 amount) {
    if (f.selector == sig:increaseSurplusCollShares(address,uint256).selector) {
        increaseSurplusCollShares(e, account, amount);
    } else if (f.selector == sig:claimSurplusCollShares(address).selector) {
        claimSurplusCollShares(e, account);
    } else if (f.selector == sig:increaseTotalSurplusCollShares(uint256).selector) {
        increaseTotalSurplusCollShares(e, amount);
    } else {
        calldataarg args;
        f(e, args);
    }
}

/// @dev Helper function to call `sweepToken` with the correct parameters IF this is the function being called
/// @dev If not, it will call the function with calldataarg
function callSweepTokenWithParams(method f, env e, address token, uint256 amount) {
    if (f.selector == sig:sweepToken(address,uint256).selector) {
        sweepToken(e, token, amount);
    } else {
        calldataarg args;
        f(e, args);
    }
}
