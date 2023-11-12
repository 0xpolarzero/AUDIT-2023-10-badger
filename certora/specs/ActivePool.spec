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
    // ActivePool public getters
    function borrowerOperationsAddress() external returns (address) envfree;
    function feeRecipientAddress() external returns (address) envfree;
    function cdpManagerAddress() external returns (address) envfree;
    function collSurplusPoolAddress() external returns (address) envfree;

    // ActivePool external getters
    function getSystemCollShares() external returns (uint256) envfree;
    function getSystemDebt() external returns (uint256) envfree;
    function getFeeRecipientClaimableCollShares() external returns (uint256) envfree;
     
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

/* ---------------------------- System collateral --------------------------- */
/// @dev Init ghost for `systemCollShares` from the ActivePool contract
ghost mathint mirror_systemCollShares {
	  init_state axiom mirror_systemCollShares == 0; 
}

/// @dev Init ghost for `feeRecipientClaimableCollShares` from the ActivePool contract
ghost mathint mirror_feeRecipientCollShares {
    init_state axiom mirror_feeRecipientCollShares == 0; 
}

/// @dev Init ghost for `sharesOf()` from the collateral contract
ghost mapping(address => mathint) mirror_sharesOf {
    init_state axiom forall address a. mirror_sharesOf[a] == 0;
}

/// @dev Mirror updates to `systemCollShares` in `mirror_systemCollShares`
hook Sstore systemCollShares uint256 newCollShares (uint256 oldCollShares) STORAGE {
    mirror_systemCollShares = newCollShares;
}

/// @dev Mirror updates to `feeRecipientClaimableCollShares` in `mirror_feeRecipientCollShares`
hook Sstore feeRecipientClaimableCollShares uint256 newCollShares (uint256 oldCollShares) STORAGE {
    mirror_feeRecipientCollShares = newCollShares;
}

/// @dev Mirror updates to `collateral.sharesOf()` (tracked in a `balances` mapping) in `mirror_sharesOf`
hook Sstore collateral.balances[KEY address a] uint256 newCollShares (uint256 oldCollShares) STORAGE {
  // havoc sumOfShares assuming sumOfShares@new() == sumOfShares@old() + newValue - oldValue;
    mirror_sharesOf[a] = newCollShares;
}

/// @dev Tracked system collateral shares should always be equal to the shares reported by the collateral contract
invariant inv_systemCollSharesCorrectlyTracked()
    mirror_systemCollShares == mirror_sharesOf[currentContract];

/// @dev Tracked fee recipient collateral shares should always be equal to the shares reported by the collateral contract
invariant inv_feeRecipientCollSharesCorrectlyTracked()
    mirror_feeRecipientCollShares == mirror_sharesOf[feeRecipientAddress()];

/* -------------------------------------------------------------------------- */
/*                                    RULES                                   */
/* -------------------------------------------------------------------------- */

use rule sanity;
use builtin rule viewReentrancy;

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

rule testRule(method f) {
  // 1 = 28948022309329048855892746252171976963317496166410141009864396001978282409986
    assert collateral.balanceOf(currentContract) == collateral.getPooledEthByShares(getSystemCollShares());
    env e;
    calldataarg args;
    f(e, args);
    assert collateral.balanceOf(currentContract) == collateral.getPooledEthByShares(getSystemCollShares());
}

/* -------------------------------------------------------------------------- */
/*                                   HELPERS                                  */
/* -------------------------------------------------------------------------- */

/// @dev Helper function to call either `increaseSurplusCollShares`, `claimSurplusCollShares` or `increaseTotalSurplusCollShares`
/// with the correct parameters IF this is the function being called
/// @dev If not, it will call the function with calldataarg
// function callCollFunctionWithParams(method f, env e, address account, uint256 amount) {
//     if (f.selector == sig:increaseSurplusCollShares(address,uint256).selector) {
//         increaseSurplusCollShares(e, account, amount);
//     } else if (f.selector == sig:claimSurplusCollShares(address).selector) {
//         claimSurplusCollShares(e, account);
//     } else if (f.selector == sig:increaseTotalSurplusCollShares(uint256).selector) {
//         increaseTotalSurplusCollShares(e, amount);
//     } else {
//         calldataarg args;
//         f(e, args);
//     }
// }