# Notes intended for judging this formal verification effort

## Modified

### Harness contracts

- `harness/CollSurplusPoolHarness.sol`: added helper functions

### Specs

- `specs/CollSurplusPool.spec`: added new specs

### Confs

- `confs/CollSurplusPool.conf`: added new confs
- `confs/EBTCToken.conf`: use harness instead of original contract
- `confs/gambit/EBTCToken.conf`: remove manual mutation (not existing)

## New

### Harness contracts

- `harness/EBTCTokenHarness`: new harness contract to add helper functions
