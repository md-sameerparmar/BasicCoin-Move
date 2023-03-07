module NamedAddr::BasicCoin {
    use std::signer;

    // const MODULE_OWNER: address = @NamedAddr;

    const ENOT_MODULE_OWNER: u64 = 0;
    const EINSUFFICIENT_BALANCE: u64 = 1;
    const EALREADY_HAS_BALANCE: u64 = 2;

    struct Coin<phantom CoinType> has store {
        value : u64
    }

    struct Balance<phantom CoinType> has key {
        coin: Coin<CoinType>
    }

    public fun publish_balance<CoinType>(account: &signer) {
        let empty_coin = Coin<CoinType> {value:0};
        assert!(!exists<Balance<CoinType>>(signer::address_of(account)),EALREADY_HAS_BALANCE);
        move_to(account, Balance<CoinType>{coin: empty_coin});
    }

    public fun mint<CoinType: drop>(mint_addr: address, amount: u64, _witness: CoinType) acquires Balance {
        deposit(mint_addr, Coin<CoinType>{value: amount});
    }

    public fun balance_of<CoinType>(owner: address): u64 acquires Balance {
        borrow_global<Balance<CoinType>>(owner).coin.value
    }

    spec balance_of{
        pragma aborts_if_is_strict;
    }
    
    public fun transfer<CoinType: drop>(from: &signer, to: address, amount: u64, _witness: CoinType) acquires Balance {
        let check = withdraw<CoinType>(signer::address_of(from), amount);
        deposit<CoinType>(to, check);
    }

    fun withdraw<CoinType>(addr: address, amount: u64): Coin<CoinType> acquires Balance{
        let balance = balance_of<CoinType>(addr);
        assert!(balance >= amount, EINSUFFICIENT_BALANCE);
        let balance_ref = &mut borrow_global_mut<Balance<CoinType>>(addr).coin.value;
        *balance_ref = balance - amount;
        Coin<CoinType> {value: amount}
    }

    fun deposit<CoinType>(addr: address, check: Coin<CoinType>) acquires Balance{
        let balance = balance_of<CoinType>(addr);
        let balance_ref = &mut borrow_global_mut<Balance<CoinType>>(addr).coin.value;
        let Coin {value} = check;
        *balance_ref = balance + value;
    }

    // #[test(account = @0x1)]
    // #[expected_failure]
    // fun mint_non_owner(account: signer) acquires Balance {
    //     publish_balance(&account);
    //     assert!(signer::address_of(&account) != MODULE_OWNER, 0);
    //     mint(&account, @0x1, 10);
    // }

    // #[test(account = @NamedAddr)]
    // fun mint_check_balance(account: signer) acquires Balance{
    //     let addr = signer::address_of(&account);
    //     publish_balance(&account);
    //     mint(&account, @NamedAddr, 42);
    //     assert!(balance_of(addr) == 42,0);
    // }

    // #[test(account = @0x1)]
    // fun publish_balance_has_zero(account: signer) acquires Balance{
    //     let addr = signer::address_of(&account);
    //     publish_balance(&account);
    //     assert!(balance_of(addr) == 0, 0);
    // }

    // #[test(account = @0x1)]
    // #[expected_failure(abort_code = EALREADY_HAS_BALANCE)]
    // fun publish_balance_already_exixts(account: signer){
    //     publish_balance(&account);
    //     publish_balance(&account);
    // }

    // #[test]
    // #[expected_failure]
    // fun balance_of__dne() acquires Balance {
    //     balance_of(@0x1);
    // }

    // #[test]
    // #[expected_failure]
    // fun withdraw_dne() acquires Balance {
    //     Coin { value: _} = withdraw(@0x1,0);
    // }

    // #[test(account = @0x1)]
    // #[expected_failure]
    // fun withdraw_too_much(account: signer) acquires Balance {
    //     let addr = signer::address_of(&account);
    //     publish_balance(&account);
    //     Coin {value: _} = withdraw(addr,1);
    // }

    // #[test(account = @NamedAddr)]
    // fun can_withdraw_amount(account: signer) acquires Balance {
    //     publish_balance(&account);
    //     let amount = 1000;
    //     let addr = signer::address_of(&account);
    //     mint(&account, addr, amount);
    //     let Coin {value} = withdraw(addr, amount);
    //     assert!(value == amount, 0)
    // }
}