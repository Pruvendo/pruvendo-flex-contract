TEMPLATE = app
CONFIG += console optimize_full c++20
CONFIG -= app_bundle
CONFIG -= qt

INCLUDEPATH += "../tokens"

SOURCES += \
        ../tokens/fungible/RootTokenContract.cpp \
        ../tokens/fungible/TONTokenWallet.cpp \
        FLeX.cpp \
        FLeXClient.cpp \
        FLeXDebot.cpp \
        Price.cpp \
        PriceXchg.cpp \
        Proxy.cpp \
        TestTradeDebot.cpp \
        TradingPair.cpp \
        XchgPair.cpp \
        freetr_debot.cpp

HEADERS += \
    ../tokens/RootTokenContract.hpp \
    ../tokens/TONTokenWallet.hpp \
    FLeX.hpp \
    FLeXClient.hpp \
    Price.hpp \
    PriceCommon.hpp \
    PriceXchg.hpp \
    Proxy.hpp \
    TradingPair.hpp \
    XchgPair.hpp
