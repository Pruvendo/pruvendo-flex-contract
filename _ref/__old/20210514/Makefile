all: Proxy.tvc FLeX.tvc TradingPair.tvc XchgPair.tvc Price.tvc PriceXchg.tvc freetr_debot.tvc tip3info.tvc FLeXClient.tvc FLeXDebot.tvc

Proxy.tvc: Proxy.cpp Proxy.hpp
	clang -o Proxy.tvc Proxy.cpp -I ../tokens -Wall

FLeX.tvc: FLeX.cpp FLeX.hpp TradingPair.hpp XchgPair.hpp Price.hpp PriceXchg.hpp PriceCommon.hpp
	clang -o FLeX.tvc FLeX.cpp -I ../tokens -Wall

TradingPair.tvc: TradingPair.cpp FLeX.hpp TradingPair.hpp Price.hpp PriceCommon.hpp
	clang -o TradingPair.tvc TradingPair.cpp -I ../tokens -Wall

XchgPair.tvc: XchgPair.cpp FLeX.hpp XchgPair.hpp PriceXchg.hpp PriceCommon.hpp
	clang -o XchgPair.tvc XchgPair.cpp -I ../tokens -Wall

Price.tvc: Price.cpp FLeX.hpp TradingPair.hpp Price.hpp PriceCommon.hpp
	clang -mtvm-refunc -o Price.tvc Price.cpp -I ../tokens -Wall

PriceXchg.tvc: PriceXchg.cpp FLeX.hpp XchgPair.hpp PriceXchg.hpp PriceCommon.hpp
	clang -mtvm-refunc -o PriceXchg.tvc PriceXchg.cpp -I ../tokens -Wall

freetr_debot.tvc: freetr_debot.cpp FLeX.hpp TradingPair.hpp XchgPair.hpp Price.hpp PriceXchg.hpp PriceCommon.hpp
	clang -o freetr_debot.tvc freetr_debot.cpp -I ../tokens -Wall

tip3info.tvc: tip3info.cpp ../tokens/TONTokenWallet.hpp ../tokens/RootTokenContract.hpp
	clang -o tip3info.tvc tip3info.cpp -I ../tokens -Wall

FLeXClient.tvc: FLeXClient.cpp ../tokens/TONTokenWallet.hpp ../tokens/RootTokenContract.hpp
	clang -o FLeXClient.tvc FLeXClient.cpp -I ../tokens -Wall

FLeXDebot.tvc: FLeXDebot.cpp ../tokens/TONTokenWallet.hpp ../tokens/RootTokenContract.hpp
	clang -o FLeXDebot.tvc FLeXDebot.cpp -I ../tokens -Wall

clean:
	rm -f *.abi
	rm -f *.tvc

