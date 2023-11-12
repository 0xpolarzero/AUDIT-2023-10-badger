// SPDX-License-Identifier: MIT

pragma solidity 0.8.17;

import "../../packages/contracts/contracts/ActivePool.sol";
import "../../packages/contracts/contracts/Dependencies/IERC20.sol";

contract ActivePoolHarness is ActivePool {
    constructor(
        address _borrowerOperationsAddress,
        address _cdpManagerAddress,
        address _collTokenAddress,
        address _collSurplusAddress,
        address _feeRecipientAddress
    )
        ActivePool(
            _borrowerOperationsAddress,
            _cdpManagerAddress,
            _collTokenAddress,
            _collSurplusAddress,
            _feeRecipientAddress
        )
    {}
}
