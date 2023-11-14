/*
verification of SortedCdps
This is an advnaced project and requires probably qunatifiers and more summarization.
see https://github.com/Certora/Examples/tree/master/CVLByExample/QuantifierExamples 
*/

/// @dev Verify on original contract:
/// certoraRun certora/confs/SortedCdps_verified.conf
/// @dev Verify against mutations:
/// certoraMutate --prover_conf certora/confs/SortedCdps_verified.conf --mutation_conf certora/confs/gambit/SortedCdps.conf

/* -------------------------------------------------------------------------- */
/*                                   METHODS                                  */
/* -------------------------------------------------------------------------- */

methods {
    // Public getters
    function cdpManager() external returns (address) envfree;
    function borrowerOperationsAddress() external returns (address) envfree;
    function maxSize() external returns (uint256) envfree;

    // Core
    function contains(bytes32 _id) external  returns (bool) envfree;
    function isFull() external  returns (bool) envfree; 
    function isEmpty() external  returns (bool) envfree;
    function getSize() external  returns (uint256) envfree;
    function getMaxSize() external  returns (uint256) envfree;
    function getFirst() external  returns (bytes32) envfree;
    function getLast() external  returns (bytes32) envfree;
    function getNext(bytes32 _id) external  returns (bytes32) envfree;
    function getPrev(bytes32 _id) external  returns (bytes32) envfree;

    /* summarizing as a deterministic and unique function. need to prove that this.
       see certora/specs/SortedCdps_DpdIds.spec  */
    function toCdpId(
        address owner,
        uint256 blockHeight,
        uint256 nonce
    ) internal returns (bytes32) => uniqueId(owner,blockHeight,nonce);

    function toCdpId(
        address owner,
        uint256 blockHeight,
        uint256 nonce
    ) external returns (bytes32) envfree;

    // CdpManager
    /* placeholder - NONDET is the default (safe) summarization but might be 
       too over apporximation for certrain properties */
    function _.getNominalICR(bytes32) external  => NONDET;
    function _.getCdpStatus(bytes32) external => NONDET;
}

/* -------------------------------------------------------------------------- */
/*                                 INVARIANTS                                 */
/* -------------------------------------------------------------------------- */

/* ----------------------------- GHOST VARIABLES ---------------------------- */
ghost uniqueId(address /*owner*/, uint256 /*blockHeight*/, uint256 /*nonce*/ ) returns bytes32 {
    axiom forall address o1. forall address o2. 
        forall uint256 b1. forall uint256 b2.
        forall uint256 n1. forall uint256 n2.
        (o1 != o2 || b1 != b2 || n1 != n2) => uniqueId(o1, b1, n1) != uniqueId(o2, b2, n2);
}

/* ------------------------------- INVARIANTS ------------------------------- */
invariant maxSizeIntegrity() 
    getSize() <= getMaxSize();

/* -------------------------------------------------------------------------- */
/*                                    RULES                                   */
/* -------------------------------------------------------------------------- */

rule reachability(method f) {
    env e;
    calldataarg args;
    f(e,args);
    satisfy true;
}

/// @dev Getter functions should never revert
/// @dev This does not include all view/pure functions, as some can indeed revert. Namely, the following:
/// - toCdpId(address,uint256,uint256)
/// - cdpOfOwnerByIndex(address,uint256)
/// - cdpOfOwnerByIdx(address,uint256,bytes32,uint256)
/// - cdpCountOf(address)
/// - getCdpCountOf(address,bytes32,uint256)
/// - getCdpsOf(address)
/// - getAllCdpsOf(address,bytes32,uint256)
/// - validInsertPosition(uint256,bytes32,bytes32)
/// - findInsertPosition(uint256,bytes32,bytes32)
rule gettersNeverRevert(method f) {
    address a;

    env e;
    calldataarg args;
    require e.msg.value == 0;
    f@withrevert(e, args);

    assert (
        f.selector == sig:getOwnerAddress(bytes32).selector ||
        f.selector == sig:nonExistId().selector ||
        f.selector == sig:contains(bytes32).selector ||
        f.selector == sig:isFull().selector ||
        f.selector == sig:isEmpty().selector ||
        f.selector == sig:getSize().selector ||
        f.selector == sig:getMaxSize().selector ||
        f.selector == sig:getFirst().selector ||
        f.selector == sig:getLast().selector ||
        f.selector == sig:getNext(bytes32).selector ||
        f.selector == sig:getPrev(bytes32).selector
    ) => !lastReverted;
}

/// @dev Functions with controled access should only be called by authorized addresses
rule accessControl(method f) {
    env e;
    calldataarg args;
    f(e, args);

    // Borrower operations or cdp manager
    assert (
        f.selector == sig:insert(address,uint256,bytes32,bytes32).selector ||
        f.selector == sig:reInsert(bytes32,uint256,bytes32,bytes32).selector
    ) => e.msg.sender == borrowerOperationsAddress() || e.msg.sender == cdpManager();

    // Cdp manager
    assert (
        f.selector == sig:remove(bytes32).selector ||
        f.selector == sig:batchRemove(bytes32[]).selector
    ) => e.msg.sender == cdpManager();
}

rule uniqunessOfId(
    address o1,  address o2,
    uint256 b1,  uint256 b2, 
    uint256 n1,  uint256 n2
) {
// calls to toCdpId are to the public solidity function which calls the internal one that is summarized
// therefore, this rule actually checks the summarization uniqueId 
assert (o1 != o2 || b1 != b2 || n1 != n2) => toCdpId(o1, b1, n1) != toCdpId(o2, b2, n2);
}

/// @dev Changes to the first/last element should happen under correct conditions
rule changeToFirstOrLast(method f) {
    bytes32 firstBefore = getFirst();
    bytes32 lastBefore = getLast();

    env e;
    calldataarg args;
    f(e,args);

    bytes32 firstAfter = getFirst();
    bytes32 lastAfter = getLast();

    assert (firstAfter != firstBefore || lastAfter != lastBefore) => (
        f.selector == sig:insert(address,uint256,bytes32,bytes32).selector ||  
        f.selector == sig:reInsert(bytes32,uint256,bytes32,bytes32).selector ||
        f.selector == sig:remove(bytes32).selector ||
        f.selector == sig:batchRemove(bytes32[]).selector
    ); 
}

/// @dev If the list is full, it cannot increase anymore
rule isFullCanNotIncrease(method f) {
    bool isFullBefore = isFull();
    uint256 sizeBefore = getSize();

    env e;
    calldataarg args;
    f(e,args);

    assert isFullBefore => getSize() <= sizeBefore;
}