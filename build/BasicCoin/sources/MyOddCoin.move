module NamedAddr::MyOddCoin {
    use std::signer;
    use NamedAddr::BasicCoin;

    struct MyOddCoin has drop{}

    const ENOT_ODD: u64 = 0;

    public fun setup_and_mint(account: &signer, amount: u64) {
        BasicCoin::publish_balance<MyOddCoin>(account);
        BasicCoin::mint<MyOddCoin>(signer::address_of(account), amount, MyOddCoin{});
    }

    public fun transfer(from: &signer, to: address, amount: u64) {
        assert!(amount % 2 == 1, ENOT_ODD);
        BasicCoin::transfer<MyOddCoin>(from, to, amount, MyOddCoin {});
    }

    #[test(from = @0x42, to = @0x10)]
    fun test_odd_success(from: signer, to: signer) {
        setup_and_mint(&from, 42);
        setup_and_mint(&to, 10);

        transfer(&from, @0x10, 7);

        assert!(BasicCoin::balance_of<MyOddCoin>(@0x42) == 35, 0);
        assert!(BasicCoin::balance_of<MyOddCoin>(@0x10) == 17, 0);
    }

    #[test(from = @0x42, to = @0x10)]
    #[expected_failure]
    fun test_not_odd_failur(from: signer, to: signer) {
        setup_and_mint(&from, 42);
        setup_and_mint(&to, 10);

        transfer(&from, @0x10, 8);
    }
}