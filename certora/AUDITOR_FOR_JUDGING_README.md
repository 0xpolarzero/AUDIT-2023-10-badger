# Notes intended for judging this formal verification effort

I thought it could be useful to provide some context on my process—maybe it can help understand it better and judge it more efficiently.

I gave my best effort covering [EBTCToken](./specs/EBTCToken.spec), [ActivePool](./specs/ActivePool.spec) and [CollSurplusPool](./specs/CollSurplusPool.spec). Unfortunately, I could not work on [SortedCdps](./specs/SortedCdps.spec) in time, that's find you will find its coverage pretty poor.

## Methodology

The following is a summary of the methodology used to find necessary checks to perform when writing rules. I believe it is especially true for large contracts. You will find it not as much applied to the `EBTCToken` contract, as I wrote the specifications early on.

- Read the contract and find all tracked variables, especially tracking balances or any kind of ownership, shares, debt, etc.
- Find all ways these variables can be modified.
- For each kind of modification (increase, decrease, set), find all possible ways it can be done.
- Write rules as follows.
    - If an increase/decrease of x happened:
    - => it happened in the y exact conditions, and by z exact amount;
    - => all other assertions (e.g. state of other users, variables) still hold true (~ invariants).

## Changes

Changes to the configuration files are minimal. Basically, I added harness contracts for `ActivePool` and `EBTCToken` to implement helper functions—that's why the configuration for these is modified. The rest is broadly new specs in existing files, and I left some notes I took during my process of first examining the `ActivePool` contract.

### Modified

**Harness contracts**

- `harness/CollSurplusPoolHarness.sol`: added helper functions
- `harness/CollateralTokenTester.sol`: formatted

**Specs**

- `specs/ActivePool.spec`: added new specs
- `specs/SortedCdps.spec`: added new specs
- `specs/CollSurplusPool.spec`: added new specs
- `specs/EBTCToken.spec`: added new specs

**Confs**

- `confs/ActivePool_verified.conf`: use harness instead of original contract
- `confs/EBTCToken_verified.conf`: use harness instead of original contract
- `confs/gambit/EBTCToken.conf`: remove manual mutation (not existing)

### New files

**Harness contracts**

- `harness/EBTCTokenHarness`: new harness contract to add helper functions
- `harness/ActivePoolHarness`: new harness contract to add helper functions

**Notes**

- `specs/NOTES_ActivePool.md`: notes during preliminary analysis of rules to verify and states to track; just as some kind of reference/documentation
