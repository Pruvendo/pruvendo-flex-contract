all: FlexWallet.tvc FlexTokenRoot.tvc TONTokenWallet.tvc RootTokenContract.tvc Wrapper.tvc TestWrapperDebot.tvc TestRootOwner.tvc TestWalletOwner.tvc tip3dbt.tvc

FlexWallet.tvc: TONTokenWallet.cpp TONTokenWallet.hpp
	clang TONTokenWallet.cpp -DTIP3_ENABLE_LEND_OWNERSHIP -DTIP3_ENABLE_BURN -mtvm-refunc -o FlexWallet.tvc

FlexWallet.hashes: FlexWallet.tvc Makefile
	tonos-cli decode stateinit --tvc FlexWallet.tvc | \
    grep -E "(code_hash|code_depth)" | \
    sed -e 's/"code_hash": "/-DTIP3_WALLET_CODE_HASH=0x/' \
        -e 's/"code_depth": "/-DTIP3_WALLET_CODE_DEPTH=/; s/",//g' | \
    tr -d '\n' | awk '{$$1=$$1};1' > FlexWallet.hashes

TONTokenWallet.hashes: TONTokenWallet.tvc Makefile
	tonos-cli decode stateinit --tvc TONTokenWallet.tvc | \
    grep -E "(code_hash|code_depth)" | \
    sed -e 's/"code_hash": "/-DTIP3_WALLET_CODE_HASH=0x/' \
        -e 's/"code_depth": "/-DTIP3_WALLET_CODE_DEPTH=/; s/",//g' | \
    tr -d '\n' | awk '{$$1=$$1};1' > TONTokenWallet.hashes

TONTokenWallet.tvc: TONTokenWallet.cpp TONTokenWallet.hpp
	clang TONTokenWallet.cpp -DTIP3_ENABLE_EXTERNAL -DTIP3_ENABLE_ALLOWANCE -DTIP3_IMPROVED_TRANSFER -mtvm-refunc -o TONTokenWallet.tvc

RootTokenContract.tvc: RootTokenContract.cpp RootTokenContract.hpp TONTokenWallet.hpp TONTokenWallet.hashes
	clang RootTokenContract.cpp $(file < TONTokenWallet.hashes) -DTIP3_ENABLE_EXTERNAL -DTIP3_ENABLE_ALLOWANCE -DTIP3_IMPROVED_TRANSFER -o RootTokenContract.tvc

FlexTokenRoot.tvc: RootTokenContract.cpp RootTokenContract.hpp TONTokenWallet.hpp FlexWallet.hashes
	clang RootTokenContract.cpp $(file < FlexWallet.hashes) -DTIP3_ENABLE_LEND_OWNERSHIP -DTIP3_ENABLE_BURN -o FlexTokenRoot.tvc

Wrapper.tvc: Wrapper.cpp Wrapper.hpp TONTokenWallet.hpp FlexWallet.hashes
	clang Wrapper.cpp -o Wrapper.tvc $(file < FlexWallet.hashes) -DTIP3_ENABLE_EXTERNAL -DTIP3_ENABLE_ALLOWANCE -DTIP3_IMPROVED_TRANSFER

TestWrapperDebot.tvc: TestWrapperDebot.cpp TONTokenWallet.hpp RootTokenContract.hpp Wrapper.hpp
	clang TestWrapperDebot.cpp -o TestWrapperDebot.tvc -mtvm-refunc -DTIP3_ENABLE_BURN -DTIP3_ENABLE_LEND_OWNERSHIP -DTIP3_IMPROVED_TRANSFER

TestRootOwner.tvc: TestRootOwner.cpp TONTokenWallet.hpp RootTokenContract.hpp
	clang TestRootOwner.cpp -o TestRootOwner.tvc

TestWalletOwner.tvc: TestWalletOwner.cpp TONTokenWallet.hpp RootTokenContract.hpp
	clang TestWalletOwner.cpp -o TestWalletOwner.tvc -DTIP3_ENABLE_EXTERNAL -DTIP3_ENABLE_ALLOWANCE -DTIP3_IMPROVED_TRANSFER

tip3dbt.tvc: tip3dbt.cpp TONTokenWallet.hpp
	clang tip3dbt.cpp -DTIP3_ENABLE_EXTERNAL -DTIP3_ENABLE_ALLOWANCE -DTIP3_IMPROVED_TRANSFER -o tip3dbt.tvc

tip3deploy.tvc: tip3deploy.cpp TONTokenWallet.hpp RootTokenContract.hpp
	clang tip3deploy.cpp -mtvm-refunc -DTIP3_ENABLE_BURN -DTIP3_ENABLE_LEND_OWNERSHIP -DTIP3_IMPROVED_TRANSFER -o tip3deploy.tvc -I ./

clean:
	rm -rf *.tvc
	rm -rf *.abi

