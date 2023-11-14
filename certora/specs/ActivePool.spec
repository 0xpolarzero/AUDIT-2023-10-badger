import "./sanity.spec";
import "./erc20.spec";

/// @dev Verify on original (harness) contract:
/// certoraRun certora/confs/ActivePool_verified.conf
/// @dev Verify against mutations:
/// certoraMutate --prover_conf certora/confs/ActivePool_verified.conf --mutation_conf certora/confs/gambit/ActivePool.conf

using CollateralTokenTester as collateral;
using MockFlashBorrower as borrower;

/* -------------------------------------------------------------------------- */
/*                                   METHODS                                  */
/* -------------------------------------------------------------------------- */

methods {
   // Helper functions
    function call_isAuthorized(address user, bytes4 functionSig) external returns (bool) envfree;
    function helper_uint32ToBytes4(uint32) external returns (bytes4) envfree;
    function helper_CdpManagerStorage_calculateFeeAllocatedToFeeRecipientAfterSync() external returns (uint256) envfree;
    function helper_CollSurplusPool_getTotalSurplusCollShares() external returns (uint256) envfree;
    function helper_getTokenBalance(address token, address target) external returns (uint256) envfree;

    // ActivePool public getters
    function MAX_BPS() external returns (uint256) envfree;
    function DECIMAL_PRECISION() external returns (uint256) envfree;
    function FLASH_SUCCESS_VALUE() external returns (bytes32) envfree;
    function flashFee(address, uint256) external returns (uint256) envfree;
    function borrowerOperationsAddress() external returns (address) envfree;
    function feeRecipientAddress() external returns (address) envfree;
    function cdpManagerAddress() external returns (address) envfree;
    function collSurplusPoolAddress() external returns (address) envfree;
    function collSurplusPoolAddress() external returns (address) envfree;
    function feeBps() external returns (uint16) envfree;
    function flashLoansPaused() external returns (bool) envfree;

    // ActivePool external getters
    function getSystemCollShares() external returns (uint256) envfree;
    function getSystemDebt() external returns (uint256) envfree;
    function getFeeRecipientClaimableCollShares() external returns (uint256) envfree;

    // ActivePool methods
    function increaseSystemCollShares(uint256) external;
    function transferSystemCollShares(address, uint256) external;
    function transferSystemCollSharesAndLiquidatorReward(address, uint256, uint256) external;
    function allocateSystemCollSharesToFeeRecipient(uint256) external;
    function claimFeeRecipientCollShares(uint256) external;
    function flashLoan(address, address, uint256, bytes) external returns (bool);
    function increaseSystemDebt(uint256) external;
    function decreaseSystemDebt(uint256) external;
    function sweepToken(address, uint256) external;
    function setFeeRecipientAddress(address) external;
    function setFeeBps(uint256) external;
    function setFlashLoansPaused(bool) external;
     
     // Collateral methods
    function collateral.balanceOf(address) external returns (uint256) envfree;
    function collateral.sharesOf(address) external returns (uint256) envfree;
    function collateral.getPooledEthByShares(uint256) external returns (uint256) envfree;
    function collateral.getSharesByPooledEth(uint256) external returns (uint256) envfree;

    // ERC3156 FlashLender
    function _.increaseTotalSurplusCollShares(uint256) external => DISPATCHER(true);
    function _.onFlashLoan(address, address, uint256, uint256, bytes) external => DISPATCHER(true);

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

/// @dev Functions with controled access should only be called by authorized addresses
rule accessControl(method f) {
    env e;
    calldataarg args;
    f(e, args);

    // Borrower operations or cdp manager
    assert (
        f.selector == sig:transferSystemCollShares(address,uint256).selector ||
        f.selector == sig:transferSystemCollSharesAndLiquidatorReward(address,uint256,uint256).selector ||
        f.selector == sig:increaseSystemDebt(uint256).selector ||
        f.selector == sig:decreaseSystemDebt(uint256).selector
    ) => e.msg.sender == borrowerOperationsAddress() || e.msg.sender == cdpManagerAddress();

    // Borrower operations
    assert (
        f.selector == sig:increaseSystemCollShares(uint256).selector
    ) => e.msg.sender == borrowerOperationsAddress();

    // Cdp manager
    assert (
        f.selector == sig:allocateSystemCollSharesToFeeRecipient(uint256).selector
    ) => e.msg.sender == cdpManagerAddress();

    // Authorized
    assert (
        f.selector == sig:claimFeeRecipientCollShares(uint256).selector ||
        f.selector == sig:sweepToken(address,uint256).selector ||
        f.selector == sig:setFeeRecipientAddress(address).selector ||
        f.selector == sig:setFeeBps(uint256).selector ||
        f.selector == sig:setFlashLoansPaused(bool).selector
    ) => call_isAuthorized(e.msg.sender, helper_uint32ToBytes4(f.selector));
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
/// 3. A function called `CpdManagerData.syncGlobalAccountingAndGracePeriod()`
///     - This will allocate part of the system collateral shares to the fee recipient
///         => The system collateral shares are decreased by a calculated amount
///         => The fee recipient collateral shares are increased by the calculated amount
/// @dev Change to `feeRecipientClaimableCollShares` should only occur in such ways:
/// 4. `feeRecipientClaimableCollShares` increased
///     - The borrower operations or cdp manager called `allocateSystemCollSharesToFeeRecipient`
///         => The fee recipient claimable collateral shares are increased by the specified amount
/// 5. `feeRecipientClaimableCollShares` decreased
///     - An authorized entity called `claimFeeRecipientCollShares`
///         => The function `CpdManagerData.syncGlobalAccountingAndGracePeriod()` is called
///         => The fee recipient claimable collateral shares are decreased by the specified amount
///         => The shares are transferred to the fee recipient
/// 6. A function called `CpdManagerData.syncGlobalAccountingAndGracePeriod()`
///     - This will allocate part of the system collateral shares to the fee recipient
///         => The system collateral shares are decreased by a calculated amount
///         => The fee recipient collateral shares are increased by the calculated amount
rule changeToCollSharesTracker(method f) {
    address account;
    address user;
    uint256 amount;
    uint256 liquidatorReward;

    uint256 systemCollSharesBefore = getSystemCollShares();
    uint256 feeRecipientCollSharesBefore = getFeeRecipientClaimableCollShares();
    uint256 collSharesBeforeContract = collateral.sharesOf(currentContract);
    uint256 collSharesBeforeFeeRecipient = collateral.sharesOf(feeRecipientAddress());
    uint256 collSharesBeforeAccount = collateral.sharesOf(account);
    uint256 collSharesBeforeBorrower = collateral.sharesOf(borrower);
    uint256 collSharesBeforeUser = collateral.sharesOf(user);
    // The collateral allocated to the fee recipient after the sync (if any)
    uint256 newAllocatedFee = helper_CdpManagerStorage_calculateFeeAllocatedToFeeRecipientAfterSync();
    // The total surplus collateral shares in the CollSurplusPool contract
    uint256 totalSurplusCollSharesBefore = helper_CollSurplusPool_getTotalSurplusCollShares();

    env e;
    callCollSharesFunctionWithParams(f, e, account, amount, liquidatorReward);

    uint256 systemCollSharesAfter = getSystemCollShares();
    uint256 feeRecipientCollSharesAfter = getFeeRecipientClaimableCollShares();
    uint256 collSharesAfterContract = collateral.sharesOf(currentContract);
    uint256 collSharesAfterFeeRecipient = collateral.sharesOf(feeRecipientAddress());
    uint256 collSharesAfterAccount = collateral.sharesOf(account);
    uint256 collSharesAfterBorrower = collateral.sharesOf(borrower);
    uint256 collSharesAfterUser = collateral.sharesOf(user);
    uint256 totalSurplusCollSharesAfter = helper_CollSurplusPool_getTotalSurplusCollShares();

    mathint expectedSystemCollSharesAfter = to_mathint(systemCollSharesBefore);
    mathint expectedFeeRecipientCollSharesAfter = to_mathint(feeRecipientCollSharesBefore);
    mathint expectedCollSharesBalanceAfterContract = to_mathint(collSharesBeforeContract);
    mathint expectedCollSharesBalanceAfterFeeRecipient = to_mathint(collSharesBeforeFeeRecipient);
    mathint expectedCollSharesBalanceAfterAccount = to_mathint(collSharesBeforeAccount);
    mathint expectedCollSharesBalanceAfterBorrower = to_mathint(collSharesBeforeBorrower);

    // There are special cases where a function makes a call to `ICdpManagerData(cdpManagerAddress).syncGlobalAccountingAndGracePeriod()`.
    // which calculates a new fee allocated to the fee recipient.
    // In these cases, we first update the values according to the calculation, then we update the values according to the function call.
    if (f.selector == sig:increaseSystemCollShares(uint256).selector) {
      expectedSystemCollSharesAfter = systemCollSharesBefore + amount;
    } else if (f.selector == sig:transferSystemCollShares(address,uint256).selector) {
      expectedSystemCollSharesAfter = systemCollSharesBefore - amount;
      expectedCollSharesBalanceAfterAccount = collSharesBeforeAccount + amount;
      expectedCollSharesBalanceAfterContract = collSharesBeforeContract - amount;
    } else if (f.selector == sig:transferSystemCollSharesAndLiquidatorReward(address,uint256,uint256).selector) {
      expectedSystemCollSharesAfter = systemCollSharesBefore - amount;
      expectedCollSharesBalanceAfterAccount = collSharesBeforeAccount + amount + liquidatorReward;
      expectedCollSharesBalanceAfterContract = collSharesBeforeContract - amount - liquidatorReward;
    } else if (f.selector == sig:allocateSystemCollSharesToFeeRecipient(uint256).selector) {
      expectedSystemCollSharesAfter = systemCollSharesBefore - amount;
      expectedFeeRecipientCollSharesAfter = feeRecipientCollSharesBefore + amount;
    } else if (f.selector == sig:claimFeeRecipientCollShares(uint256).selector) {
      // Update with the new value from global accounting + direct function scope
      expectedSystemCollSharesAfter = systemCollSharesBefore - newAllocatedFee;
      expectedFeeRecipientCollSharesAfter = feeRecipientCollSharesBefore + newAllocatedFee - amount;

      expectedCollSharesBalanceAfterContract = collSharesBeforeContract - amount;
      expectedCollSharesBalanceAfterFeeRecipient = collSharesBeforeFeeRecipient + amount;
    } else if (f.selector == sig:flashLoan(address,address,uint256,bytes).selector) {
      uint256 fee = flashFee(collateral, amount);

      // We can't expect the balance of the contract because the borrower might send back more than expected
      expectedCollSharesBalanceAfterFeeRecipient = collSharesBeforeFeeRecipient + fee;
      expectedCollSharesBalanceAfterBorrower = collSharesBeforeBorrower - fee;
    } else if (
        f.selector == sig:setFeeBps(uint256).selector ||
        f.selector == sig:setFeeRecipientAddress(address).selector ||
        f.selector == sig:setFlashLoansPaused(bool).selector ||
        f.selector == sig:sweepToken(address,uint256).selector
    ) {
      expectedFeeRecipientCollSharesAfter = feeRecipientCollSharesBefore + newAllocatedFee;
      expectedSystemCollSharesAfter = systemCollSharesBefore - newAllocatedFee;
    }
    
    require account != currentContract && account != feeRecipientAddress() && account != borrower;
    // Verify that the tracked shares and balances are updated correctly
    assert (
        to_mathint(systemCollSharesAfter) == expectedSystemCollSharesAfter &&
        to_mathint(feeRecipientCollSharesAfter) == expectedFeeRecipientCollSharesAfter &&
        // In case of a flash loan the borrower might send back more than required
        (f.selector == sig:flashLoan(address,address,uint256,bytes).selector
            ? to_mathint(collSharesAfterContract) >= expectedCollSharesBalanceAfterContract
            : to_mathint(collSharesAfterContract) == expectedCollSharesBalanceAfterContract) &&
        to_mathint(collSharesAfterFeeRecipient) == expectedCollSharesBalanceAfterFeeRecipient &&
        to_mathint(collSharesAfterAccount) == expectedCollSharesBalanceAfterAccount &&
        to_mathint(collSharesAfterBorrower) <= expectedCollSharesBalanceAfterBorrower
    );

    // Verify that if there is a decrease in system collateral shares though one of these functions
    // > There was enough tracked collateral shares before
    assert (systemCollSharesAfter < systemCollSharesBefore && (
        f.selector == sig:transferSystemCollShares(address,uint256).selector ||
        f.selector == sig:transferSystemCollSharesAndLiquidatorReward(address,uint256,uint256).selector ||
        f.selector == sig:allocateSystemCollSharesToFeeRecipient(uint256).selector
    )) => systemCollSharesBefore >= amount;
    // Same for `claimFeeRecipientCollShares`
    assert (
        feeRecipientCollSharesAfter < feeRecipientCollSharesBefore &&
        f.selector == sig:claimFeeRecipientCollShares(uint256).selector
    ) => to_mathint(feeRecipientCollSharesBefore) >= amount + newAllocatedFee;

    // Check that the total surplus collateral shares was updated (if `_transferCollSharesWithContractHooks` is called).
    assert (
        account == collSurplusPoolAddress() && (
            f.selector == sig:transferSystemCollShares(address,uint256).selector ||
            f.selector == sig:transferSystemCollSharesAndLiquidatorReward(address,uint256,uint256).selector
        )
    ) => to_mathint(totalSurplusCollSharesAfter) == totalSurplusCollSharesBefore + amount;

    // Balances should not change for other users
    require user != account && user != currentContract && user != feeRecipientAddress();
    assert collSharesAfterUser == collSharesBeforeUser;
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
    // > The function is `increaseSystemDebt` or `decreaseSystemDebt`
    assert systemDebtAfter != systemDebtBefore => (
        // > Either the function is `increaseSystemDebt` => The system debt is increased by the specified amount
        (f.selector == sig:increaseSystemDebt(uint256).selector && to_mathint(systemDebtAfter) == systemDebtBefore + amount) ||
        // > Or the function is `decreaseSystemDebt` => The system debt is decreased by the specified amount
        (f.selector == sig:decreaseSystemDebt(uint256).selector && to_mathint(systemDebtAfter) == systemDebtBefore - amount)
    );
}

/// @dev "Sweeping" of arbitrary tokens from the contract should only occur in the following conditions:
/// 1. The caller is authorized
/// 2. The function called is `sweepToken`
/// 3. The token being swept is NOT the collateral token
/// 4. The amount being swept is less than or equal to the current balance of the contract
/// => The amount of the token should be transferred from the contract to the feeRecipient
rule sweepOfArbitraryToken(method f) {
    address user;
    address token;
    uint256 amount;
    uint256 beforeContract = helper_getTokenBalance(token, currentContract);
    uint256 beforeRecipient = helper_getTokenBalance(token, feeRecipientAddress());
    uint256 beforeUser = helper_getTokenBalance(token, user);

    env e;
    callSweepTokenWithParams(f, e, token, amount);

    uint256 afterContract = helper_getTokenBalance(token, currentContract);
    uint256 afterRecipient = helper_getTokenBalance(token, feeRecipientAddress());
    uint256 afterUser = helper_getTokenBalance(token, user);

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
        amount <= beforeContract &&
        // actual transfer of tokens
        to_mathint(afterContract) == beforeContract - amount &&
        to_mathint(afterRecipient) == beforeRecipient + amount &&
        // no other balances change
        afterUser == beforeUser
    );
}

/// @dev Flash loans should only occur in the following conditions:
/// 1. The amount is > 0 and <= to the maxium flash loan for this token (`collateral.balanceOf(address(this))`)
/// 2. The token is the collateral
/// 3. Flash loans are not paused
/// 4. The contract transfers `amount` of collateral to the IERC3156FlashBorrower borrower
/// 4. The IERC3156FlashBorrower borrower `onFlashLoan` callback returns `FLASH_SUCCESS_VALUE`
/// 5. The contract receives back `amount + ((amount * feeBps) / MAX_BPS)` of collateral
/// 7. The balance of the contract is >= to the balance of the contract (as in `collateral.getPooledEthByShares(systemCollShares)`
/// 6. The shares of the contract are >= to the shares tracked by `systemCollShares` (although already enforced as an invariant)
/// 7. The collateral share rate does not change (`collateral.getPooledEthByShares(DECIMAL_PRECISION)`)
/// 8. The function returns true
rule flashLoan(method f) {
    address token;
    address account;
    address user;
    uint256 amount;
    bytes data;

    uint256 systemCollSharesBefore = getSystemCollShares();
    uint256 collSharesBeforeContract = collateral.sharesOf(currentContract);
    uint256 collSharesBeforeBorrower = collateral.sharesOf(borrower);
    uint256 collSharesBeforeFeeRecipient = collateral.sharesOf(feeRecipientAddress());
    uint256 collSharesBeforeAccount = collateral.sharesOf(account);
    uint256 collSharesBeforeUser = collateral.sharesOf(user);
    uint256 balanceBeforeContract = collateral.balanceOf(currentContract);
    uint256 balanceBeforeBorrower = collateral.balanceOf(borrower);
    uint256 balanceBeforeFeeRecipient = collateral.balanceOf(feeRecipientAddress());
    uint256 rateBefore = collateral.getPooledEthByShares(DECIMAL_PRECISION());
    uint256 fee = flashFee(collateral, amount);
    bool flashLoansPausedBefore = flashLoansPaused();

    env e;
    bool success;
    // if (f.selector == sig:make_flashLoan(address,address,uint256,bytes).selector) {
    if (f.selector == sig:flashLoan(address,address,uint256,bytes).selector) {
        // (borrower, success) = make_flashLoan(token, amount, data);
        success = flashLoan(e, borrower, token, amount, data);
        // if transferSystemCollShares or transferSystemCollSharesAndLiquidatorReward is called, pass amount
    } else if (f.selector == sig:transferSystemCollShares(address,uint256).selector) {
        transferSystemCollShares(e, account, amount);
        success = false;
    } else if (f.selector == sig:transferSystemCollSharesAndLiquidatorReward(address,uint256,uint256).selector) {
        transferSystemCollSharesAndLiquidatorReward(e, account, amount, 0);
        success = false;
    } else {
        calldataarg args;
        f(e, args);
        success = false;
    }
    

    uint256 systemCollSharesAfter = getSystemCollShares();
    uint256 collSharesAfterContract = collateral.sharesOf(currentContract);
    uint256 collSharesAfterBorrower = collateral.sharesOf(borrower);
    uint256 collSharesAfterFeeRecipient = collateral.sharesOf(feeRecipientAddress());
    uint256 collSharesAfterAccount = collateral.sharesOf(account);
    uint256 collSharesAfterUser = collateral.sharesOf(user);
    uint256 balanceAfterContract = collateral.balanceOf(currentContract);
    uint256 balanceAfterBorrower = collateral.balanceOf(borrower);
    uint256 balanceAfterFeeRecipient = collateral.balanceOf(feeRecipientAddress());
    uint256 rateAfter = collateral.getPooledEthByShares(DECIMAL_PRECISION());
    bool flashLoansPausedAfter = flashLoansPaused();

    // amount: 1
    // transfer 0 to borrower (getSharesByPooledEth(1) == 0)
    // fee for 1 is 1
    // transfer back 2 from the borrower

    // require borrower._lender == currentContract; ???
    // Verify that if the flash loan is successful
    // > The following conditions are met:
    assert success => (
        // > The amount is > 0 and <= to the maxium flash loan for this token (`collateral.balanceOf(address(this))`)
        amount > 0 && amount <= balanceBeforeContract &&
        // > The borrower has at least the fee amount of collateral
        balanceBeforeBorrower >= fee &&
        // > The token is the collateral
        token == collateral &&
        // > Flash loans are not paused
        !flashLoansPausedBefore && !flashLoansPausedAfter &&
        // > The IERC3156FlashBorrower borrower `onFlashLoan` callback returns `FLASH_SUCCESS_VALUE()`
    //     borrower.onFlashLoan(e, borrower, token, amount, fee, data) == FLASH_SUCCESS_VALUE() &&
        // > The contract receives back at least the correct amount of collateral
        collSharesAfterContract >= collSharesBeforeContract &&
        // > The fee recipient receives their fee
        // We need to use shares and convert balances with getSharesByPooledEth to be consistent with the contract
        // Basically a fee of 1 will be converted to 0 shares, so we need to reproduce the same rounding here.
        to_mathint(collSharesAfterFeeRecipient) == collSharesBeforeFeeRecipient + collateral.getSharesByPooledEth(fee) &&
        // > The borrower is left with no more than their initial balance - the fee
        to_mathint(collSharesAfterBorrower) <= collSharesBeforeBorrower - collateral.getSharesByPooledEth(fee) &&
        // > The collateral share/ETH rate does not change
        rateAfter == rateBefore &&

        // @audit-info The following checks absolutely work:
        // > The balance of the contract is >= to the equivalent from tracked shares
        balanceAfterContract >= collateral.getPooledEthByShares(systemCollSharesAfter) &&
        // > The shares of the contract are >= to the shares tracked by `systemCollShares`
        collSharesAfterContract >= systemCollSharesAfter &&
        // @audit-info But it might be more consistent to check against a value cached _before_ the call.
        // `systemCollShares` _should_ not change during the call, there is no reason, but it might be just better
        // to use a cached value from before the call.
        // Also, it does save a SLOAD in any case to cache it at the beginning.
        // > Just check the same as above but against cached values
        balanceAfterContract >= balanceBeforeContract &&
        collSharesAfterContract >= systemCollSharesBefore
    );

    // The fee should be calculated correctly
    assert to_mathint(fee) == (amount * feeBps()) / MAX_BPS();

    // Balances should not change for other users, except if the function is `transferSystemCollShares` or `transferSystemCollSharesAndLiquidatorReward`
    require account != currentContract && account != feeRecipientAddress() && account != borrower && account != collSurplusPoolAddress();
    assert (
        f.selector == sig:transferSystemCollShares(address,uint256).selector ||
        f.selector == sig:transferSystemCollSharesAndLiquidatorReward(address,uint256,uint256).selector
    ) => (
        to_mathint(collSharesAfterAccount) == collSharesBeforeAccount + amount
    );
    require user != currentContract && user != feeRecipientAddress() && user != borrower && user != collSurplusPoolAddress() && user != account;
    assert collSharesAfterUser == collSharesBeforeUser;
}

/// @dev Setters should only be called by authorized addresses and update the correct value
/// 1. `setFeeRecipientAddress` (authorized)
///     => The global accounting is updated
///     => The fee recipient is updated
/// 2. `setFeeBps` (authorized)
///     => The global accounting is updated
///     => The fee bps is updated
/// 3. `setFlashLoansPaused` (authorized)
///     => The global accounting is updated
///     => The flash loans paused is updated
/// @dev The global accounting updates are already verified in `changeToCollSharesTracker`
rule setters(method f) {
    address newFeeRecipient;
    uint256 newFeeBps;
    bool newFlashLoansPaused;

    address feeRecipientBefore = feeRecipientAddress();
    uint256 feeBpsBefore = feeBps();
    bool flashLoansPausedBefore = flashLoansPaused();

    env e;
    if (f.selector == sig:setFeeRecipientAddress(address).selector) {
        setFeeRecipientAddress(e, newFeeRecipient);
    } else if (f.selector == sig:setFeeBps(uint256).selector) {
        setFeeBps(e, newFeeBps);
    } else if (f.selector == sig:setFlashLoansPaused(bool).selector) {
        setFlashLoansPaused(e, newFlashLoansPaused);
    } else {
        calldataarg args;
        f(e, args);
    }

    address feeRecipientAfter = feeRecipientAddress();
    uint256 feeBpsAfter = feeBps();
    bool flashLoansPausedAfter = flashLoansPaused();

    // Verify that if the fee recipient is updated
    // > The caller is authorized and the update is correct
    assert feeRecipientAfter != feeRecipientBefore => (
        call_isAuthorized(e.msg.sender, helper_uint32ToBytes4(f.selector)) &&
        feeRecipientAfter == newFeeRecipient
    );

    // Verify that if the fee bps is updated
    // > The caller is authorized and the update is correct
    assert feeBpsAfter != feeBpsBefore => (
        call_isAuthorized(e.msg.sender, helper_uint32ToBytes4(f.selector)) &&
        feeBpsAfter == newFeeBps
    );

    // Verify that if the flash loans paused status is updated
    // > The caller is authorized and the update is correct
    assert flashLoansPausedAfter != flashLoansPausedBefore => (
        call_isAuthorized(e.msg.sender, helper_uint32ToBytes4(f.selector)) &&
        flashLoansPausedAfter == newFlashLoansPaused
    );
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
    } else if (f.selector == sig:claimFeeRecipientCollShares(uint256).selector) {
        claimFeeRecipientCollShares(e, amount);
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