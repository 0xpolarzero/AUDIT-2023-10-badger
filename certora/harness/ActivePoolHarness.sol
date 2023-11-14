// SPDX-License-Identifier: MIT

pragma solidity 0.8.17;

import "../../packages/contracts/contracts/ActivePool.sol";
import "../../packages/contracts/contracts/Dependencies/IERC20.sol";
import "./MockFlashBorrower.sol";

contract ActivePoolHarness is ActivePool {
    IERC3156FlashBorrower public immutable borrower;

    constructor(
        address _borrowerOperationsAddress,
        address _cdpManagerAddress,
        address _collTokenAddress,
        address _collSurplusAddress,
        address _feeRecipientAddress,
        // Add a borrower
        MockFlashBorrower _borrower
    )
        ActivePool(
            _borrowerOperationsAddress,
            _cdpManagerAddress,
            _collTokenAddress,
            _collSurplusAddress,
            _feeRecipientAddress
        )
    {
        borrower = _borrower;
    }

    function call_isAuthorized(address user, bytes4 functionSig) external view returns (bool) {
        return isAuthorized(user, functionSig);
    }

    function helper_uint32ToBytes4(uint32 x) external pure returns (bytes4) {
        return bytes4(x);
    }

    /// @dev The following is a reproduction of functions from CdpManagerStorage to calculate the collateral allocated
    /// to the fee recipient after syncing the global accounting and grace period.
    /// `ICdpManagerData(cdpManagerAddress).syncGlobalAccountingAndGracePeriod()`
    function helper_CdpManagerStorage_calculateFeeAllocatedToFeeRecipientAfterSync()
        external
        view
        returns (uint256 newAllocatedFee)
    {
        ICdpManagerData cdpManager = ICdpManagerData(cdpManagerAddress);

        // _readStEthIndex()
        uint256 oldIndex = cdpManager.stEthIndex();
        uint256 newIndex = collateral.getPooledEthByShares(DECIMAL_PRECISION);

        // _syncGlobalAccounting()
        if (newIndex > oldIndex && cdpManager.totalStakes() > 0) {
            (newAllocatedFee,,) = cdpManager.calcFeeUponStakingReward(newIndex, oldIndex);
        } else {
            newAllocatedFee = 0;
        }

        // _takeSplitAndUpdateFeePerUnit()
        if (newAllocatedFee >= systemCollShares) {
            // In this case it will revert, so we might just return 0 so it doesn't change the fee
            newAllocatedFee = 0;
        }
    }

    /// @dev Returns the total surplus pool in the CollSurplusPool contract
    function helper_CollSurplusPool_getTotalSurplusCollShares() external view returns (uint256) {
        return ICollSurplusPool(collSurplusPoolAddress).getTotalSurplusCollShares();
    }

    /// @dev Returns the balance of an account for a specific token
    function helper_getTokenBalance(address token, address target) external view returns (uint256) {
        return IERC20(token).balanceOf(target);
    }
}
