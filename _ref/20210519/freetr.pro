TEMPLATE = app
CONFIG += console optimize_full c++20
CONFIG -= app_bundle
CONFIG -= qt

INCLUDEPATH += "../tokens"

SOURCES += \
        ../tokens/RootTokenContract.cpp \
        ../tokens/TONTokenWallet.cpp \
        FLeX.cpp \
        FLeXClient.cpp \
        FLeXDebot.cpp \
        Price.cpp \
        PriceXchg.cpp \
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
    TradingPair.hpp \
    XchgPair.hpp
