# Notes intended for judging this formal verification effort

## Methodology

The following is a summary of the methodology used to find necessary checks to perform when writing rules. I believe it is especially true for large contracts. You will find it not as much applied to the `EBTCToken` contract, as I wrote the specifications early on.

- Read the contract and find all tracked variables, especially tracking balances or any kind of ownership, shares, debt, etc.
- Find all ways these variables can be modified.
- For each kind of modification (increase, decrease, set), find all possible ways it can be done.
- Write rules as follows.
    - If an increase/decrease of x happened:
    - => it happened in the y exact conditions, and by z exact amount;
    - => all other assertions (e.g. state of other users, variables) still hold true (~ invariants).

## Modified

### Harness contracts

- `harness/CollSurplusPoolHarness.sol`: added helper functions
- `harness/CollateralTokenTester.sol`: formatted

### Specs

- `specs/ActivePool.spec`: added new specs
- `specs/SortedCdps.spec`: added new specs
- `specs/CollSurplusPool.spec`: added new specs
- `specs/EBTCToken.spec`: added new specs

### Confs

- `confs/EBTCToken_verified.conf`: use harness instead of original contract
- `confs/gambit/EBTCToken.conf`: remove manual mutation (not existing)

## New

### Harness contracts

- `harness/EBTCTokenHarness`: new harness contract to add helper functions
- `harness/ActivePoolHarness`: new harness contract to add helper functions

### Notes

- `specs/NOTES_ActivePool.md`: notes during preliminary analysis of rules to verify and states to track
