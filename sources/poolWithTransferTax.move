// Copyright (c) 2022, Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

/// Example implementation of a liquidity Pool for Sui
/// Adapted to include a transfer tax that sends funds to a treasury.
/// Adaptation made by: https://github.com/joaoaccaldeira
///
/// - Only module publisher can create new Pools.
/// - For simplicity's sake all swaps are done with SUI coin.
/// Generalizing to swaps between non-SUI coin types requires a few more generics, but is otherwise straightforward
/// - Fees are customizable per Pool.
/// - Max stored value for both tokens is: U64_MAX / 10_000
///
/// To publish a new pool, a type is required. Eg:
/// ```
/// module me::my_pool {
///   use myDefi::pool;
///   use sui::coin::Coin;
///   use sui::sui::SUI;
///   use sui::tx_context::TxContext;
///
///   struct POOL_TEAM has drop {}
///
///   entry fun create_pool<T>(
///     token: Coin<T>,
///     sui: Coin<SUI>,
///     fee_lp: u64,
///     fee_treasury: u64,
///     ctx: &mut TxContext
///   ) {
///     pool::create_pool(POOL_TEAM {}, token, sui, fee_lp, fee_treasury, ctx)
///   }
/// }
/// ```
///
/// This solution is rather simple and is based on the example from the Move repo:
/// https://github.com/move-language/move/blob/main/language/documentation/examples/experimental/coin-swap/sources/CoinSwap.move
module myDefi::poolWithTransferTax {
    use sui::object::{Self, UID};
    use sui::coin::{Self, Coin};
    use sui::balance::{Self, Supply, Balance};
    use sui::sui::SUI;
    use sui::transfer;
    use sui::math;
    use sui::tx_context::{Self, TxContext};

    /// For when supplied Coin is zero.
    const EZeroAmount: u64 = 0;

    /// For when pool fee is set incorrectly.
    /// Allowed values are: [0-10000).
    const EWrongFee: u64 = 1;

    /// For when someone tries to swap in an empty pool.
    const EReservesEmpty: u64 = 2;

    /// For when initial LSP amount is zero.
    const EShareEmpty: u64 = 3;

    /// For when someone attempts to add more liquidity than u128 Math allows.
    const EPoolFull: u64 = 4;

    /// For when someone other than the owner attempts to withdraw from the treasury
    const ENotOwner: u64 = 5;

    /// The integer scaling setting for fees calculation.
    const FEE_SCALING: u128 = 10000;

    /// The max value that can be held in one of the Balances of
    /// a Pool. U64 MAX / FEE_SCALING
    const MAX_POOL_VALUE: u64 = {
        18446744073709551615 / 10000
    };

    /// The Pool token that will be used to mark the pool share
    /// of a liquidity provider. The first type parameter stands
    /// for the witness type of a pool. The seconds is for the
    /// coin held in the pool.
    struct LSP<phantom P, phantom T> has drop {}

    /// The pool with exchange.
    ///
    /// - `fee_lp` should be in the range: [0-10000), meaning
    /// that 1000 is 100% and 1 is 0.1%
    struct Pool<phantom P, phantom T> has key {
        id: UID,
        sui: Balance<SUI>,
        token: Balance<T>,
        lsp_supply: Supply<LSP<P, T>>,
        /// Fee Percent is denominated in basis points.
        fee_lp: u64,
        /// Fee Percent Treasury
        fee_treasury: u64,
    }

    struct Treasury <phantom P, phantom T> has key {
        id: UID,
        sui: Balance<SUI>,
        owner: address,
    }

    /// Module initializer is empty - to publish a new Pool one has
    /// to create a type which will mark LSPs.
    fun init(_: &mut TxContext) {
    }

    /// Treasury functions
    entry fun change_treasury_owner<P,T>(treasury: &mut Treasury<P,T>, new_owner: address, ctx: &mut TxContext) {
        assert!(tx_context::sender(ctx) == treasury.owner, ENotOwner);
        treasury.owner = new_owner;
    }

    fun deposit_into_treasury<P, T>(treasury: &mut Treasury<P,T>, sui: Coin<SUI>) {
        balance::join(
            &mut treasury.sui,
            coin::into_balance(sui)
        );
    }

    entry fun withdraw_amount_from_treasury<P, T>(treasury: &mut Treasury<P,T>, amount: u64, ctx: &mut TxContext){
        assert!(tx_context::sender(ctx) == treasury.owner, ENotOwner);
        let split_balance = balance::split(&mut treasury.sui, amount);
        transfer::transfer(
            coin::from_balance(split_balance, ctx),
            treasury.owner
        );
    }

    entry fun withdraw_total_from_treasury<P, T>(treasury: &mut Treasury<P,T>, ctx: &mut TxContext){
        assert!(tx_context::sender(ctx) == treasury.owner, ENotOwner);

        let total_amount = balance::value(&treasury.sui);
        let split_balance = balance::split(&mut treasury.sui, total_amount);

        transfer::transfer(
            coin::from_balance(split_balance, ctx),
            treasury.owner
        );
    }

    /// Create new `Pool` for token `T`. Each Pool holds a `Coin<T>`
    /// and a `Coin<SUI>`. Swaps are available in both directions.
    ///
    /// Share is calculated based on Uniswap's constant product formula:
    ///  liquidity = sqrt( X * Y )
    public fun create_pool<P: drop, T>(
        _: P,
        token: Coin<T>,
        sui: Coin<SUI>,
        fee_lp: u64,
        fee_treasury: u64,
        ctx: &mut TxContext
    ): Coin<LSP<P, T>> {

        transfer::share_object(Treasury<P,T> { 
            id: object::new(ctx), 
            sui: balance::zero<SUI>(), 
            owner: tx_context::sender(ctx) 
        });

        let sui_amt = coin::value(&sui);
        let tok_amt = coin::value(&token);

        assert!(sui_amt > 0 && tok_amt > 0, EZeroAmount);
        assert!(sui_amt < MAX_POOL_VALUE && tok_amt < MAX_POOL_VALUE, EPoolFull);
        assert!(fee_lp >= 0 && fee_lp < 10000, EWrongFee);
        assert!(fee_treasury >= 0 && fee_lp < 2000, EWrongFee);

        // Initial share of LSP is the sqrt(a) * sqrt(b)
        let share = math::sqrt(sui_amt) * math::sqrt(tok_amt);
        let lsp_supply = balance::create_supply(LSP<P, T> {});
        let lsp = balance::increase_supply(&mut lsp_supply, share);

        transfer::share_object(Pool {
            id: object::new(ctx),
            token: coin::into_balance(token),
            sui: coin::into_balance(sui),
            lsp_supply,
            fee_lp,
            fee_treasury
        });

        coin::from_balance(lsp, ctx)
    }


    /// Entrypoint for the `swap_sui` method. Sends swapped token
    /// to sender.
    entry fun swap_sui_<P, T>(
        pool: &mut Pool<P, T>, sui: Coin<SUI>, treasury: &mut Treasury<P,T>, ctx: &mut TxContext
    ) {
        transfer::transfer(
            swap_sui(pool, sui, treasury, ctx),
            tx_context::sender(ctx)
        )
    }

    /// Swap `Coin<SUI>` for the `Coin<T>`.
    /// Returns Coin<T>.
    public fun swap_sui<P, T>(
        pool: &mut Pool<P, T>, sui: Coin<SUI>, treasury: &mut Treasury<P,T>, ctx: &mut TxContext
    ): Coin<T> {
        assert!(coin::value(&sui) > 0, EZeroAmount);

        let sui_balance = coin::into_balance(sui);
        let sui_balance_value = balance::value(&sui_balance);
        let sui_balance_to_treasury = balance::split(&mut sui_balance, ((sui_balance_value*pool.fee_treasury as u128)/FEE_SCALING as u64));

        // Deposits the taxed amount to the treasury
        deposit_into_treasury(treasury, coin::from_balance(sui_balance_to_treasury, ctx));

        // Calculate the output amount - fee
        let (sui_reserve, token_reserve, _) = get_amounts(pool);

        assert!(sui_reserve > 0 && token_reserve > 0, EReservesEmpty);

        let output_amount = get_input_price(
            balance::value(&sui_balance),
            sui_reserve,
            token_reserve,
            pool.fee_lp
        );

        balance::join(&mut pool.sui, sui_balance);
        coin::take(&mut pool.token, output_amount, ctx)
    }

    /// Entry point for the `swap_token` method. Sends swapped SUI
    /// to the sender.
    entry fun swap_token_<P, T>(
        pool: &mut Pool<P, T>, token: Coin<T>, treasury: &mut Treasury<P,T>, ctx: &mut TxContext
    ) {
        transfer::transfer(
            swap_token(pool, token, treasury, ctx),
            tx_context::sender(ctx)
        )
    }

    /// Swap `Coin<T>` for the `Coin<SUI>`.
    /// Returns the swapped `Coin<SUI>`.
    public fun swap_token<P, T>(
        pool: &mut Pool<P, T>, token: Coin<T>, treasury: &mut Treasury<P,T>, ctx: &mut TxContext
    ): Coin<SUI> {
        assert!(coin::value(&token) > 0, EZeroAmount);

        let tok_balance = coin::into_balance(token);
        let (sui_reserve, token_reserve, _) = get_amounts(pool);

        assert!(sui_reserve > 0 && token_reserve > 0, EReservesEmpty);

        let output_amount = get_input_price(
            balance::value(&tok_balance),
            token_reserve,
            sui_reserve,
            pool.fee_lp
        );

        balance::join(&mut pool.token, tok_balance);

        let output_to_treasury = ((output_amount*pool.fee_treasury as u128)/FEE_SCALING as u64);

        // Deposits the taxed amount to the treasury
        deposit_into_treasury(treasury, coin::take(&mut pool.sui, output_to_treasury, ctx));

        coin::take(&mut pool.sui, output_amount-output_to_treasury, ctx)
    }

    /// Entrypoint for the `add_liquidity` method. Sends `Coin<LSP>` to
    /// the transaction sender.
    entry fun add_liquidity_<P, T>(
        pool: &mut Pool<P, T>, sui: Coin<SUI>, token: Coin<T>, ctx: &mut TxContext
    ) {
        transfer::transfer(
            add_liquidity(pool, sui, token, ctx),
            tx_context::sender(ctx)
        );
    }

    /// Add liquidity to the `Pool`. Sender needs to provide both
    /// `Coin<SUI>` and `Coin<T>`, and in exchange he gets `Coin<LSP>` -
    /// liquidity provider tokens.
    public fun add_liquidity<P, T>(
        pool: &mut Pool<P, T>, sui: Coin<SUI>, token: Coin<T>, ctx: &mut TxContext
    ): Coin<LSP<P, T>> {
        assert!(coin::value(&sui) > 0, EZeroAmount);
        assert!(coin::value(&token) > 0, EZeroAmount);

        let sui_balance = coin::into_balance(sui);
        let tok_balance = coin::into_balance(token);

        let (sui_amount, tok_amount, lsp_supply) = get_amounts(pool);

        let sui_added = balance::value(&sui_balance);
        let tok_added = balance::value(&tok_balance);
        let share_minted = math::min(
            (sui_added * lsp_supply) / sui_amount,
            (tok_added * lsp_supply) / tok_amount
        );

        let sui_amt = balance::join(&mut pool.sui, sui_balance);
        let tok_amt = balance::join(&mut pool.token, tok_balance);

        assert!(sui_amt < MAX_POOL_VALUE, EPoolFull);
        assert!(tok_amt < MAX_POOL_VALUE, EPoolFull);

        let balance = balance::increase_supply(&mut pool.lsp_supply, share_minted);
        coin::from_balance(balance, ctx)
    }

    /// Entrypoint for the `remove_liquidity` method. Transfers
    /// withdrawn assets to the sender.
    entry fun remove_liquidity_<P, T>(
        pool: &mut Pool<P, T>,
        lsp: Coin<LSP<P, T>>,
        ctx: &mut TxContext
    ) {
        let (sui, token) = remove_liquidity(pool, lsp, ctx);
        let sender = tx_context::sender(ctx);

        transfer::transfer(sui, sender);
        transfer::transfer(token, sender);
    }

    /// Remove liquidity from the `Pool` by burning `Coin<LSP>`.
    /// Returns `Coin<T>` and `Coin<SUI>`.
    public fun remove_liquidity<P, T>(
        pool: &mut Pool<P, T>,
        lsp: Coin<LSP<P, T>>,
        ctx: &mut TxContext
    ): (Coin<SUI>, Coin<T>) {
        let lsp_amount = coin::value(&lsp);

        // If there's a non-empty LSP, we can
        assert!(lsp_amount > 0, EZeroAmount);

        let (sui_amt, tok_amt, lsp_supply) = get_amounts(pool);
        let sui_removed = (sui_amt * lsp_amount) / lsp_supply;
        let tok_removed = (tok_amt * lsp_amount) / lsp_supply;

        balance::decrease_supply(&mut pool.lsp_supply, coin::into_balance(lsp));

        (
            coin::take(&mut pool.sui, sui_removed, ctx),
            coin::take(&mut pool.token, tok_removed, ctx)
        )
    }

    /// Public getter for the price of SUI in token T.
    /// - How much SUI one will get if they send `to_sell` amount of T;
    public fun sui_price<P, T>(pool: &Pool<P, T>, to_sell: u64): u64 {
        let (sui_amt, tok_amt, _) = get_amounts(pool);
        get_input_price(to_sell, tok_amt, sui_amt, pool.fee_lp)
    }

    /// Public getter for the price of token T in SUI.
    /// - How much T one will get if they send `to_sell` amount of SUI;
    public fun token_price<P, T>(pool: &Pool<P, T>, to_sell: u64): u64 {
        let (sui_amt, tok_amt, _) = get_amounts(pool);
        get_input_price(to_sell, sui_amt, tok_amt, pool.fee_lp)
    }


    /// Get most used values in a handy way:
    /// - amount of SUI
    /// - amount of token
    /// - total supply of LSP
    public fun get_amounts<P, T>(pool: &Pool<P, T>): (u64, u64, u64) {
        (
            balance::value(&pool.sui),
            balance::value(&pool.token),
            balance::supply_value(&pool.lsp_supply)
        )
    }

    public fun get_treasury_balance_value<P, T>(treasury: &mut Treasury<P, T>) : u64 {
        balance::value(&treasury.sui)
    }

    public fun get_treasury_owner<P,T>(treasury: &mut Treasury<P,T>) : address {
        treasury.owner
    }

    /// Calculate the output amount minus the fee - 0.3%
    public fun get_input_price(
        input_amount: u64, input_reserve: u64, output_reserve: u64, fee_lp: u64
    ): u64 {
        // up casts
        let (
            input_amount,
            input_reserve,
            output_reserve,
            fee_lp
        ) = (
            (input_amount as u128),
            (input_reserve as u128),
            (output_reserve as u128),
            (fee_lp as u128)
        );

        let input_amount_with_fee = input_amount * (FEE_SCALING - fee_lp);
        let numerator = input_amount_with_fee * output_reserve;
        let denominator = (input_reserve * FEE_SCALING) + input_amount_with_fee;

        (numerator / denominator as u64)
    }

    #[test_only]
    public fun init_for_testing(ctx: &mut TxContext) {
        init(ctx)
    }

    #[test_only]
    public fun withdraw_amount_for_testing<P,T> (treasury: &mut Treasury<P,T>, amount: u64, ctx: &mut TxContext) {
        withdraw_amount_from_treasury(treasury, amount, ctx);
    }

    #[test_only]
    public fun withdraw_total_for_testing<P,T>(treasury: &mut Treasury<P,T>, ctx: &mut TxContext) {
        withdraw_total_from_treasury(treasury, ctx);
    }
}

/// Example implementation of a token that uses the LP w/ Treasury transfer tax
module myDefi::aenova {
    use myDefi::poolWithTransferTax;
    use sui::sui::SUI;
    use sui::tx_context::{Self, TxContext};
    use sui::balance::{Self, Supply};
    use sui::object::{Self, UID};
    use sui::coin::{Self, Coin};
    use sui::transfer;

    struct Aenova has drop {}

    struct TreasuryCap has key, store {
        id: UID,
        supply: Supply<Aenova>
    }

    entry fun create_pool<T>(
        token: Coin<T>,
        sui: Coin<SUI>,
        fee_lp: u64,
        fee_treasury: u64,
        _treasury_cap: &TreasuryCap,
        ctx: &mut TxContext
    ) {
        let lsp = poolWithTransferTax::create_pool(Aenova {}, token, sui, fee_lp, fee_treasury, ctx);
        transfer::transfer(lsp, tx_context::sender(ctx));
    }


    /// Initializer
    fun init(ctx: &mut TxContext) {
        let sender = tx_context::sender(ctx);

        let treasury_cap = TreasuryCap {
            id: object::new(ctx),
            supply: balance::create_supply(Aenova {})
        };

        let total_supply = balance::increase_supply<Aenova>(&mut treasury_cap.supply, 1000000000);
        let coin_total_supply = coin::from_balance(total_supply, ctx);

        transfer::transfer(coin_total_supply, sender);
        transfer::transfer(treasury_cap, sender);
    }

    #[test_only]
    public fun init_for_testing(ctx: &mut TxContext) {
        init(ctx)
    }
    
}


#[test_only]
/// Tests for the pool module.
module myDefi::pool_tests {
    use sui::sui::SUI;
    use sui::coin::{mint_for_testing as mint, destroy_for_testing as burn};
    use sui::test_scenario::{Self as test, Scenario, next_tx, ctx};
    use myDefi::poolWithTransferTax::{Self, Pool, LSP, Treasury};

    /// Gonna be our test token.
    struct BEEP {}

    /// A witness type for the pool creation;
    /// The pool provider's identifier.
    struct POOLEY has drop {}

    const SUI_AMT: u64 = 1000000000;
    const BEEP_AMT: u64 = 1000000;

    // Tests section
    #[test] fun test_init_pool() { test_init_pool_(&mut scenario()) }
    #[test] fun test_add_liquidity() { test_add_liquidity_(&mut scenario()) }
    #[test] fun test_swap_sui() { test_swap_sui_(&mut scenario()) }
    #[test] fun test_swap_tok() { test_swap_tok_(&mut scenario()) }
    #[test] fun test_withdraw_almost_all() { test_withdraw_almost_all_(&mut scenario()) }
    #[test] fun test_withdraw_all() { test_withdraw_all_(&mut scenario()) }
    #[test] fun test_withdraw_treasury_by_owner() { test_withdraw_treasury_by_owner_(&mut scenario())}

    #[test]
    #[expected_failure(abort_code = 5)]
    fun test_withdraw_treasury_total_fail() {
        test_withdraw_treasury_total_fail_(&mut scenario())
    }

    #[test]
    #[expected_failure(abort_code = 5)]
    fun test_withdraw_treasury_amount_fail() {
        test_withdraw_treasury_amount_fail_(&mut scenario())
    }

    // Non-sequential tests
    #[test] fun test_math() { test_math_(&mut scenario()) }

    /// Init a Pool with a 1_000_000 BEEP and 1_000_000_000 SUI;
    /// Set the ratio BEEP : SUI = 1 : 1000.
    /// Set LSP token amount to 1000;
    fun test_init_pool_(test: &mut Scenario) {
        let (owner, _) = people();

        next_tx(test, &owner); {
            poolWithTransferTax::init_for_testing(ctx(test));
        };

        next_tx(test, &owner); {
            let lsp = poolWithTransferTax::create_pool(
                POOLEY {},
                mint<BEEP>(BEEP_AMT, ctx(test)),
                mint<SUI>(SUI_AMT, ctx(test)),
                3,
                50,
                ctx(test)
            );

            assert!(burn(lsp) == 31622000, 0);
        };

        next_tx(test, &owner); {
            let pool = test::take_shared<Pool<POOLEY, BEEP>>(test);
            let pool_mut = test::borrow_mut(&mut pool);
            let treasury = test::take_shared<Treasury<POOLEY, BEEP>>(test);
            let treasury_mut = test::borrow_mut(&mut treasury);
            let (amt_sui, amt_tok, lsp_supply) = poolWithTransferTax::get_amounts(pool_mut);

            let treasuryBalanceValue = poolWithTransferTax::get_treasury_balance_value<POOLEY, BEEP>(treasury_mut);
            assert!(treasuryBalanceValue == 0, 0);
            let treasuryOwner = poolWithTransferTax::get_treasury_owner<POOLEY, BEEP>(treasury_mut);
            assert!(treasuryOwner == owner, 0);

            assert!(lsp_supply == 31622000, 0);
            assert!(amt_sui == SUI_AMT, 0);
            assert!(amt_tok == BEEP_AMT, 0);

            test::return_shared(test, pool);
            test::return_shared(test, treasury)
        };
    }

    /// Expect LP tokens to double in supply when the same values passed
    fun test_add_liquidity_(test: &mut Scenario) {
        test_init_pool_(test);

        let (_, theguy) = people();

        next_tx(test, &theguy); {
            let pool = test::take_shared<Pool<POOLEY, BEEP>>(test);
            let pool_mut = test::borrow_mut(&mut pool);
            let (amt_sui, amt_tok, lsp_supply) = poolWithTransferTax::get_amounts(pool_mut);

            let lsp_tokens = poolWithTransferTax::add_liquidity(
                pool_mut,
                mint<SUI>(amt_sui, ctx(test)),
                mint<BEEP>(amt_tok, ctx(test)),
                ctx(test)
            );

            assert!(burn(lsp_tokens) == lsp_supply, 1);

            test::return_shared(test, pool)
        };
    }

    /// The other guy tries to exchange 5_000_000 sui for ~ 5000 BEEP,
    /// minus the commission that is paid to the pool.
    fun test_swap_sui_(test: &mut Scenario) {
        test_init_pool_(test);

        let (_, the_guy) = people();

        next_tx(test, &the_guy); {
            let pool = test::take_shared<Pool<POOLEY, BEEP>>(test);
            let pool_mut = test::borrow_mut(&mut pool);
            let treasury = test::take_shared<Treasury<POOLEY, BEEP>>(test);
            let treasury_mut = test::borrow_mut(&mut treasury);

            let treasuryBalanceValue = poolWithTransferTax::get_treasury_balance_value<POOLEY, BEEP>(treasury_mut);
            assert!(treasuryBalanceValue == 0, 0);

            let token = poolWithTransferTax::swap_sui(pool_mut, mint<SUI>(5000000, ctx(test)), treasury_mut, ctx(test));

            // Check the value of the coin received by the guy.
            // Due to rounding problem the value is not precise
            // (works better on larger numbers).
            let burnedAmount = burn(token);
            assert!(burnedAmount < 4950, 1);
            
            treasuryBalanceValue = poolWithTransferTax::get_treasury_balance_value<POOLEY, BEEP>(treasury_mut);
            assert!(treasuryBalanceValue > 0, 0);

            test::return_shared(test, pool);
            test::return_shared(test, treasury);
        };
    }

    /// The owner swaps back BEEP for SUI and expects an increase in price.
    /// The sent amount of BEEP is 1000, initial price was 1 BEEP : 1000 SUI;
    fun test_swap_tok_(test: &mut Scenario) {
        test_swap_sui_(test);

        let (owner, _) = people();

        next_tx(test, &owner); {
            let pool = test::take_shared<Pool<POOLEY, BEEP>>(test);
            let pool_mut = test::borrow_mut(&mut pool);
            let treasury = test::take_shared<Treasury<POOLEY, BEEP>>(test);
            let treasury_mut = test::borrow_mut(&mut treasury);

            let treasuryBalanceValueBeforeLastSwap = poolWithTransferTax::get_treasury_balance_value<POOLEY, BEEP>(treasury_mut);

            let sui = poolWithTransferTax::swap_token(pool_mut, mint<BEEP>(1000, ctx(test)), treasury_mut, ctx(test));

            // Actual win is 1005971, which is ~ 0.6% profit
            assert!(burn(sui) > 1000000u64, 2);

            let treasuryBalanceValue = poolWithTransferTax::get_treasury_balance_value<POOLEY, BEEP>(treasury_mut);
            assert!(treasuryBalanceValue > treasuryBalanceValueBeforeLastSwap, 0);

            test::return_shared(test, pool);
            test::return_shared(test, treasury);
        };
    }

    /// The owner should successfully withdraw the funds from the treasury
    fun test_withdraw_treasury_by_owner_(test: &mut Scenario) {
        test_swap_sui_(test);

        let (owner, _) = people();

        next_tx(test, &owner); {
            let pool = test::take_shared<Pool<POOLEY, BEEP>>(test);
            let treasury = test::take_shared<Treasury<POOLEY, BEEP>>(test);
            let treasury_mut = test::borrow_mut(&mut treasury);

            // Withdraw half of the treasury funds
            let treasuryBalanceValueBeforeLastSwap = poolWithTransferTax::get_treasury_balance_value<POOLEY, BEEP>(treasury_mut);
            poolWithTransferTax::withdraw_amount_for_testing(treasury_mut, treasuryBalanceValueBeforeLastSwap/2, ctx(test));

            // Check that operation was successful
            let treasuryBalanceValueAfterWithdraw = poolWithTransferTax::get_treasury_balance_value<POOLEY, BEEP>(treasury_mut);
            assert!(treasuryBalanceValueAfterWithdraw > treasuryBalanceValueBeforeLastSwap/3 && treasuryBalanceValueAfterWithdraw < treasuryBalanceValueBeforeLastSwap*2/3, 0);

            // Withdraw the remaining total of the treasury funds
            poolWithTransferTax::withdraw_total_for_testing(treasury_mut, ctx(test));

            // Check that operation was successful
            let treasuryBalanceValueAfterTotalWithdraw = poolWithTransferTax::get_treasury_balance_value<POOLEY, BEEP>(treasury_mut);
            assert!(treasuryBalanceValueAfterTotalWithdraw == 0, 0);

            test::return_shared(test, pool);
            test::return_shared(test, treasury);
        };
    }

    /// Other users other than the owner should not be able to withdraw the funds from the treasury
    fun test_withdraw_treasury_total_fail_(test: &mut Scenario) {
        test_swap_sui_(test);

        let (_, bad_actor) = people();

        next_tx(test, &bad_actor); {
            let pool = test::take_shared<Pool<POOLEY, BEEP>>(test);
            let treasury = test::take_shared<Treasury<POOLEY, BEEP>>(test);
            let treasury_mut = test::borrow_mut(&mut treasury);

            // Attempt to Withdraw all of the treasury funds - operation should fail
            poolWithTransferTax::withdraw_total_for_testing(treasury_mut, ctx(test));

            test::return_shared(test, pool);
            test::return_shared(test, treasury);
        };
    }

    /// Other users other than the owner should not be able to withdraw the funds from the treasury
    fun test_withdraw_treasury_amount_fail_(test: &mut Scenario) {
        test_swap_sui_(test);

        let (_, bad_actor) = people();

        next_tx(test, &bad_actor); {
            let pool = test::take_shared<Pool<POOLEY, BEEP>>(test);
            let treasury = test::take_shared<Treasury<POOLEY, BEEP>>(test);
            let treasury_mut = test::borrow_mut(&mut treasury);

            // Attempt to Withdraw half of the treasury funds - operation should fail
            let treasuryBalanceValueBeforeLastSwap = poolWithTransferTax::get_treasury_balance_value<POOLEY, BEEP>(treasury_mut);
            poolWithTransferTax::withdraw_amount_for_testing(treasury_mut, treasuryBalanceValueBeforeLastSwap/2, ctx(test));

            test::return_shared(test, pool);
            test::return_shared(test, treasury);
        };
    }

    /// Withdraw (MAX_LIQUIDITY - 1) from the pool
    fun test_withdraw_almost_all_(test: &mut Scenario) {
        test_swap_tok_(test);

        let (owner, _) = people();

        // someone tries to pass (MINTED_LSP - 1) and hopes there will be just 1 BEEP
        next_tx(test, &owner); {
            let lsp = mint<LSP<POOLEY, BEEP>>(31622000 - 1, ctx(test));
            let pool = test::take_shared<Pool<POOLEY, BEEP>>(test);
            let pool_mut = test::borrow_mut(&mut pool);

            let (sui, tok) = poolWithTransferTax::remove_liquidity(pool_mut, lsp, ctx(test));
            let (sui_reserve, tok_reserve, lsp_supply) = poolWithTransferTax::get_amounts(pool_mut);

            assert!(lsp_supply == 1, 3);
            assert!(tok_reserve > 0, 3); // actually 1 BEEP is left
            assert!(sui_reserve > 0, 3);

            burn(sui);
            burn(tok);

            test::return_shared(test, pool);
        }
    }

    /// The owner tries to withdraw all liquidity from the pool.
    fun test_withdraw_all_(test: &mut Scenario) {
        test_swap_tok_(test);

        let (owner, _) = people();

        next_tx(test, &owner); {
            let lsp = mint<LSP<POOLEY, BEEP>>(31622000, ctx(test));
            let pool = test::take_shared<Pool<POOLEY, BEEP>>(test);
            let pool_mut = test::borrow_mut(&mut pool);

            let (sui, tok) = poolWithTransferTax::remove_liquidity(pool_mut, lsp, ctx(test));
            let (sui_reserve, tok_reserve, lsp_supply) = poolWithTransferTax::get_amounts(pool_mut);

            assert!(sui_reserve == 0, 3);
            assert!(tok_reserve == 0, 3);
            assert!(lsp_supply == 0, 3);

            // make sure that withdrawn assets
            assert!(burn(sui) > 1000000000, 3);
            assert!(burn(tok) < 1000000, 3);

            test::return_shared(test, pool);
        };
    }

    /// This just tests the math.
    fun test_math_(_: &mut Scenario) {
        let u64_max = 18446744073709551615;
        let max_val = u64_max / 10000;

        // Try small values
        assert!(poolWithTransferTax::get_input_price(10, 1000, 1000, 0) == 9, 0);

        // Even with 0 comission there's this small loss of 1
        assert!(poolWithTransferTax::get_input_price(10000, max_val, max_val, 0) == 9999, 0);
        assert!(poolWithTransferTax::get_input_price(1000, max_val, max_val, 0) == 999, 0);
        assert!(poolWithTransferTax::get_input_price(100, max_val, max_val, 0) == 99, 0);
    }

    // utilities
    fun scenario(): Scenario { test::begin(&@0x1) }
    fun people(): (address, address) { (@0xBEEF, @0x1337) }
}
