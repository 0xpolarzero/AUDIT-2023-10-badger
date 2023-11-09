// SPDX-License-Identifier: MIT

pragma solidity 0.8.17;

import "../../packages/contracts/contracts/CollSurplusPool.sol";
import "../../packages/contracts/contracts/Dependencies/IERC20.sol";

contract CollSurplusPoolHarness is CollSurplusPool {
    constructor(
        address _borrowerOperationsAddress,
        address _cdpManagerAddress,
        address _activePoolAddress,
        address _collTokenAddress
    ) CollSurplusPool(_borrowerOperationsAddress, _cdpManagerAddress, _activePoolAddress, _collTokenAddress) {}

    function call_isAuthorized(address user, bytes4 functionSig) external view returns (bool) {
        return isAuthorized(user, functionSig);
    }

    function helper_uint32ToBytes4(uint32 x) external pure returns (bytes4) {
        return bytes4(x);
    }

    function helper_getTokenBalance(address token, address target) external view returns (uint256) {
        return IERC20(token).balanceOf(target);
    }
}
