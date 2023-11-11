# Notes for writing rules

## Global states

### Variables to track

- **`systemCollShares`**: deposited collateral tracker
    
    - increased by `increaseSystemCollShares`
    
    - decreased by `transferSystemCollShares`, `transferSystemCollSharesAndLiquidatorReward`, `allocateSystemCollSharesToFeeRecipient`

- **`systemDebt`**: debt tracker
    
    - increased by `increaseSystemDebt`
    
    - decreased by `decreaseSystemDebt`

- **`feeRecipientCollShares`**: coll shares claimable by fee recipient
    
    - increased by `allocateSystemCollSharesToFeeRecipient`
    
    - decreased by `claimFeeRecipientCollShares`

### Balances to track

- Balance in collateral for:
    
    - contract (ActivePool)
    - fee recipient
    - account (caller and/or specified as `_account`)
    - other users

- Balance in other tokens for:
    
    - contract (ActivePool)
    - fee recipient
    - account (caller and/or specified as `_account`)
    - other users

## Functions flow

### Collateral shares

**`transferSystemCollShares(_account, _shares)`** - BO or CDPM

1. requires `systemCollShares >= _shares`
2. decreases `systemCollShares` by `_shares`
3. transfers stETH shares to `_account`
    - if `_account` is `collateralSurplusPool` => `increaseTotalSurplusCollShares(_shares)`

**`transferSystemCollSharesAndLiquidatorReward(_account, _shares, _liquidationRewardShares)`** - BO or CDPM

1. requires `systemCollShares >= _shares + _liquidationRewardShares`
2. decreases `systemCollShares` by `_shares`
3. transfers stETH shares (`_shares + _liquidationRewardShares`) to `_account`
      - if `_account` is `collateralSurplusPool` => `increaseTotalSurplusCollShares(_shares)`

**`allocateSystemCollSharesToFeeRecipient(_shares)`** - CDPM

1. requires `systemCollShares >= _shares`
2. decreases `systemCollShares` by `_shares`
3. increases `feeRecipientCollShares` by `_shares`

### Debt

**`increaseSystemDebt(_amount)`** - BO or CDPM
    
1. increases systemDebt by _amount

**`decreaseSystemDebt(_amount)`** - BO or CDPM

1. DOES NOT require `systemDebt >= _amount`
2. decreases `systemDebt` by `_amount`

**`increaseSystemCollShares(_amount)`** - BO

1. increases `systemCollShares` by `_amount`

### Fee recipient

**`claimFeeRecipientCollShares(_shares)`** - authorized

1. calls `CdpManager.syncGlobalAccountingAndGracePeriod()` (see `CdpManagerStorage.sol`)
    - updates global index & fee-per-unit variables
    - toggles grace period
    => supposed to "help the system to accrue split fee"
2. requires `feeRecipientCollShares >= _shares`
3. decreases `feeRecipientCollShares` by `_shares`
4. transfers stETH shares to `feeRecipientAddress`

**`sweepTokens(_token, _amount)`** - authorized

1. calls `CdpManager.syncGlobalAccountingAndGracePeriod()` (see above)
2. requires `_token` is not stETH
2. requires contract balance of `_token >= _amount`
3. transfers `_amount` of `_token` to `feeRecipientAddress`

**`setFeeRecipientAddress(_newFeeRecipientAddress)`** - authorized

1. calls `CdpManager.syncGlobalAccountingAndGracePeriod()` (see above)
2. requires `_newFeeRecipientAddress != address(0)`
3. sets `feeRecipientAddress` to `_newFeeRecipientAddress`

### Flash loans

**`flashLoan(IERC3156FlashBorrower receiver, token, amount, data)`**

1. requires `amount > 0`
2. requires `amount <= maxFlashLoan(token)`
3. -> transfers amount of collateral to receiver
4. requires `receiver.onFlashLoan(caller, token, amount, flashFee(token, amount), data)` to return `keccak256("ERC3156FlashBorrower.onFlashLoan")`
5. <- transfers `amount + flashFee(token, amount)` of collateral from receiver back to contract
6. (invariant) requires collateral balance of `contract >= old balance` && `collateral.getPooledEthByShares(systemCollShares)`
      - double check is unnecessary but we might as well include it
7. (invariant) requires collateral shares of `contract >= old shares` && `systemCollShares`
      - same
8. (invariant) requires `new rate == old rate` (`collateral.getPooledEthByShares(DECIMAL_PRECISION)`)
9. returns `true`

**`flashFee(token, amount)`**

1. requires `token` is stETH (collateral)
2. requires `!flashLoansPaused`
3. returns `amount * feeBps / MAX_BPS`

**`maxFlashLoan(token)`**

1. if `token != stETH` or `flashLoansPaused`
      - returns `0`
2. else
      - returns `collateral.balanceOf(address(this))`

**`setFeeBps(_newFeeBps)`** - authorized

1. calls `CdpManager.syncGlobalAccountingAndGracePeriod()` (see above)
2. requires `_newFeeBps <= MAX_FEE_BPS`
3. sets `feeBps` to `_newFeeBps`

**`setFlashLoansPaused(_paused)`** - authorized

1. calls `CdpManager.syncGlobalAccountingAndGracePeriod()` (see above)
2. sets `flashLoansPaused` to `_paused`