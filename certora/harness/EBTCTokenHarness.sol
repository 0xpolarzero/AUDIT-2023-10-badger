// SPDX-License-Identifier: MIT

pragma solidity 0.8.17;

import "../../packages/contracts/contracts/EBTCToken.sol";
import "../../packages/contracts/contracts/Dependencies/IERC20.sol";

contract EBTCTokenHarness is EBTCToken {
    constructor(address _cdpManagerAddress, address _borrowerOperationsAddress, address _authorityAddress)
        EBTCToken(_cdpManagerAddress, _borrowerOperationsAddress, _authorityAddress)
    {}

    function call_isAuthorized(address user, bytes4 functionSig) public view returns (bool) {
        return isAuthorized(user, functionSig);
    }

    function call_isBOOrCdpMOrAuth(address user, bytes4 functionSig) external view returns (bool) {
        return isAuthorized(user, functionSig) || user == borrowerOperationsAddress || user == cdpManagerAddress;
    }

    function call_isValidTransfer(address from, address to) external view returns (bool) {
        return (
            from != address(0) && to != address(0) && to != address(this) && to != cdpManagerAddress
                && to != borrowerOperationsAddress
        );
    }

    function helper_uint32ToBytes4(uint32 x) external pure returns (bytes4) {
        return bytes4(x);
    }

    function helper_addressZero() external pure returns (address) {
        return address(0);
    }

    function helper_maxUint256() external pure returns (uint256) {
        return type(uint256).max;
    }

    function helper_recoverAddress(
        address owner,
        address spender,
        uint256 amount,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external view returns (address) {
        bytes32 PERMIT_TYPEHASH = 0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9;
        uint256 nonce = _nonces[owner];

        bytes32 digest = keccak256(
            abi.encodePacked(
                "\x19\x01",
                domainSeparator(),
                keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, amount, nonce - 1, deadline))
            )
        );

        return ecrecover(digest, v, r, s);
    }
}
