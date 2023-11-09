import "./sanity.spec";
import "./erc20.spec";

/// @dev Verify on original (harness) contract:
/// certoraRun certora/confs/CollSurplusPool_verified.conf
/// @dev Verify against mutations:
/// certoraMutate --prover_conf certora/confs/CollSurplusPool_verified.conf --mutation_conf certora/confs/gambit/CollSurplusPool.conf

using CollateralTokenTester as collateral;

/* -------------------------------------------------------------------------- */
/*                                   METHODS                                  */
/* -------------------------------------------------------------------------- */

methods {
    function call_isAuthorized(address user, bytes4 functionSig) external  returns (bool) envfree;
    function borrowerOperationsAddress() external  returns (address) envfree;
    function feeRecipientAddress() external  returns (address) envfree;

    function helper_getTokenBalance(address token, address target) external  returns (uint256) envfree;
    function helper_uint32ToBytes4(uint32 x) external  returns (bytes4) envfree;

    function sweepToken(address token, uint256 amount) external;

    // collateral methods
    function collateral.balanceOf(address) external returns (uint256) envfree;
    function collateral.sharesOf(address) external returns (uint256) envfree;
}

/* -------------------------------------------------------------------------- */
/*                                    RULES                                   */
/* -------------------------------------------------------------------------- */

/// @dev Sanity check that the functions are indeed reachable
rule reachability(method f) {
    env e;
    calldataarg args;
    f(e,args);
    satisfy true;
}

/// @dev Change to the collateral balance of the contract should only occur in the following conditions:
/// 1. The caller is authorized
/// 2. The caller is the borrowerOperationsAddress
/// -> The balance should be reduced
rule changeToCollateralBalance(method f) {
    uint256 before = collateral.balanceOf(currentContract);

    env e;
    calldataarg args;
    f(e,args);

    uint256 after = collateral.balanceOf(currentContract);
    
    assert after < before =>  
        (call_isAuthorized(e.msg.sender, helper_uint32ToBytes4(f.selector)) || e.msg.sender == borrowerOperationsAddress()); 
}

/// @dev Any "sweeping" of tokens from the contract should only occur in the following conditions:
/// 1. The caller is authorized to call `sweepToken`
/// 2. The function called is `sweepToken`
/// 3. The token being swept is NOT the collateral token
/// 4. The amount being swept is less than or equal to the current balance of the contract
/// 5. The amount is greater than 0
/// 6. The recipient of the swept tokens is NOT the contract itself
/// -> The balance of the contract should be reduced by the amount swept
/// -> The balance of the recipient should be increased by the amount swept
rule sweepToken(method f) {
    address token; uint256 amount;
    uint256 beforeContract = helper_getTokenBalance(token, currentContract);
    uint256 beforeRecipient = helper_getTokenBalance(token, feeRecipientAddress());

    env e;
    callSweepTokenWithParams(f, e, token, amount);

    uint256 afterContract = helper_getTokenBalance(token, currentContract);
    uint256 afterRecipient = helper_getTokenBalance(token, feeRecipientAddress());

    assert (call_isAuthorized(e.msg.sender, helper_uint32ToBytes4(sig:sweepToken(address,uint256).selector)) && f.selector == sig:sweepToken(address,uint256).selector && token != collateral && to_mathint(amount) <= to_mathint(beforeContract) && to_mathint(amount) > 0 && feeRecipientAddress() != currentContract) => 
        (to_mathint(afterContract) == to_mathint(beforeContract - amount) && to_mathint(afterRecipient) == to_mathint(beforeRecipient + amount));
}

/* -------------------------------------------------------------------------- */
/*                                   HELPERS                                  */
/* -------------------------------------------------------------------------- */

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
