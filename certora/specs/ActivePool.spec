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
    // mirror_systemCollShares = mirror_systemCollShares + (newCollShares - oldCollShares);
    havoc mirror_systemCollShares assuming mirror_systemCollShares@new == mirror_systemCollShares@old + newCollShares - oldCollShares;
    // mirror_systemCollShares = newCollShares;
}

/// @dev Mirror updates to `feeRecipientClaimableCollShares` in `mirror_feeRecipientClaimableCollShares`
hook Sstore feeRecipientCollShares uint256 newCollShares (uint256 oldCollShares) STORAGE {
    // mirror_feeRecipientClaimableCollShares = mirror_feeRecipientClaimableCollShares + (newCollShares - oldCollShares);
    havoc mirror_feeRecipientClaimableCollShares assuming mirror_feeRecipientClaimableCollShares@new == mirror_feeRecipientClaimableCollShares@old + newCollShares - oldCollShares;
}

/// @dev Mirror updates to `collateral.sharesOf()` (tracked in a `balances` mapping) in `mirror_sharesOf`
hook Sstore collateral.balances[KEY address a] uint256 newCollShares (uint256 oldCollShares) STORAGE {
    mirror_sharesOf[a] = mirror_sharesOf[a] + (newCollShares - oldCollShares);
    // havoc mirror_sharesOf[a] assuming mirror_sharesOf@new[a] == mirror_sharesOf@old[a] + newCollShares - oldCollShares;
}

/// @dev Shares reported by the collateral contract for ActivePool 
/// should always be >= to the tracked shares for both the system and the fee recipient
/// It could be greater since anyone can send tokens to the contract, but it should never be less
invariant inv_systemCollSharesCorrectlyTracked()
    mirror_sharesOf[currentContract] >= mirror_systemCollShares + mirror_feeRecipientClaimableCollShares;

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