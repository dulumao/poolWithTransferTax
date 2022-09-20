# Implementation of a Liquidity Pool with a transfer tax

This is an adaptation of the pool example made by Mysten Labs that can be found at https://github.com/MystenLabs/sui/blob/main/sui_programmability/examples/defi/sources/pool.move to include a transfer tax.

Cryptocurrencies that have a transfer tax are very common in a lot of in most EVM chains. With this code you can create one of these tokens yourself, by following the "aenova" example in the code.

## Features:

* The transfer tax sends the funds to a treasury object that is owned by the owner. 
* Only the owner can withdraw funds from this object.
* The transfer tax is set upon creation of the pool.
