-------------------------------- MODULE bank --------------------------------


EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

\* Constants

CONSTANTS ETH, BTC, DOGE
CONSTANTS EscrowAcc, Acc1, Acc2, Acc3, Acc4, Acc5

ChainNames == {ETH, BTC} \*, DOGE}
CoinDenominations == ChainNames

AccountNames == {EscrowAcc, Acc1, Acc2} \*, Acc3, Acc4, Acc5}

MAX_INT_HEIGHT == 1
MAX_INT == 0..MAX_INT_HEIGHT
GENESIS_SUPPLY == [ c \in CoinDenominations |-> MAX_INT_HEIGHT]

\* Type


CoinType == [CoinDenominations -> MAX_INT]

AccountType == [AccountNames -> CoinType]

TotalSupplyType == [CoinDenominations -> MAX_INT]

ChainType == [ChainNames -> AccountType]

ChannelType == {{x, y}: x, y \in ChainNames}

\* Vars

VARIABLE chains
VARIABLE totalSupply

vars == << chains, totalSupply >>

\* Helpers

\* Here f is a function of DOMAIN -> Int, S is the subset of DOMAIN to calculate the sum over
RECURSIVE Sum(_,_)
Sum(f,S) == IF S = {} THEN 0
            ELSE 
                LET x == CHOOSE x \in S : TRUE
                IN  f[x] + Sum(f, S \ {x})

\* Transitions  
    
LocalTransfer(sender, receiver, denomination, amount) ==
    /\ sender /= receiver
    /\  LET 
        chainName == denomination
        senderBalance == chains[chainName][sender][denomination]
        newSenderBalance == senderBalance - amount  
        receiverBalance == chains[chainName][receiver][denomination]
        newReceiverBalance == receiverBalance + amount 
        IN 
        /\ senderBalance >= amount
        /\ chains' = [chains EXCEPT 
                        ![chainName][sender][denomination] = newSenderBalance, 
                        ![chainName][receiver][denomination] = newReceiverBalance]
        /\ UNCHANGED << totalSupply >>

\* Specification

Init ==
    /\ \E c \in ChainType:
        /\ chains = c
        /\ \A denom \in CoinDenominations:
            /\ Sum([acc \in AccountNames |-> c[denom][acc][denom]], DOMAIN c[denom]) = GENESIS_SUPPLY[denom]
        /\ totalSupply = GENESIS_SUPPLY

Next == 
    \* Local transfer
    \/  \E chain \in ChainNames, sender, receiver \in AccountNames, denom \in CoinDenominations:
            \E amt \in 0..chains[chain][sender][denom]:
                /\ LocalTransfer(sender, receiver, denom, amt)

Spec == Init /\ [][Next]_vars

\* Invariants

TypeOK == /\ chains \in ChainType
          /\ totalSupply \in TotalSupplyType

TotalSupplyCorrect == 
    \A denom \in CoinDenominations:
        LET
            chainName == denom
            amountInAccounts == [acc \in AccountNames |-> chains[chainName][acc][denom]]
        IN totalSupply[denom] = Sum(amountInAccounts, DOMAIN chains[chainName])

NoOverdrafts == 
    \A chainName \in ChainNames, acc \in AccountNames, denom \in CoinDenominations: 
        chains[chainName][acc][denom] >= 0

\* Just a temporary debugging helper invariant
\* TEMP_SupplyDoesNotIncrease == 
\*     /\ \A denom \in CoinDenominations:
\*         /\ Sum([acc \in AccountNames |-> accounts[acc][denom]], DOMAIN accounts) = GENESIS_SUPPLY[denom]

=============================================================================
