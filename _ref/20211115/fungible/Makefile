all: FlexWallet.tvc FlexTokenRoot.tvc TONTokenWallet.tvc RootTokenContract.tvc Wrapper.tvc TestWrapperDebot.tvc TestRootOwner.tvc TestWalletOwner.tvc tip3dbt.tvc

FlexWallet.tvc: TONTokenWallet.cpp TONTokenWallet.hpp
	clang TONTokenWallet.cpp -DTIP3_ENABLE_LEND_OWNERSHIP -DTIP3_ENABLE_BURN -mtvm-refunc -o FlexWallet.tvc

TONTokenWallet.tvc: TONTokenWallet.cpp TONTokenWallet.hpp
	clang TONTokenWallet.cpp -DTIP3_ENABLE_EXTERNAL -DTIP3_ENABLE_ALLOWANCE -DTIP3_IMPROVED_TRANSFER -mtvm-refunc -o TONTokenWallet.tvc

RootTokenContract.tvc: RootTokenContract.cpp RootTokenContract.hpp TONTokenWallet.hpp
	clang RootTokenContract.cpp -DTIP3_ENABLE_EXTERNAL -DTIP3_ENABLE_ALLOWANCE -DTIP3_IMPROVED_TRANSFER -o RootTokenContract.tvc

FlexTokenRoot.tvc: RootTokenContract.cpp RootTokenContract.hpp TONTokenWallet.hpp
	clang RootTokenContract.cpp -DTIP3_ENABLE_LEND_OWNERSHIP -DTIP3_ENABLE_BURN -o FlexTokenRoot.tvc

Wrapper.tvc: Wrapper.cpp Wrapper.hpp TONTokenWallet.hpp
	clang Wrapper.cpp -o Wrapper.tvc -DTIP3_ENABLE_EXTERNAL -DTIP3_ENABLE_ALLOWANCE -DTIP3_IMPROVED_TRANSFER

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

