-------------------------------- MODULE bank --------------------------------


EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

\* Constants

CONSTANTS ETH, BTC, DOGE
CONSTANTS Acc1, Acc2, Acc3, Acc4, Acc5

CoinDenominations == {ETH, BTC} \*, DOGE}
AccountNames == {Acc1, Acc2} \*, Acc3, Acc4, Acc5}

\* Type


CoinType == [CoinDenominations -> Int]

AccountType == [AccountNames -> CoinType]

TotalSupplyType == [CoinDenominations -> Int]

\* Vars

VARIABLE accounts
VARIABLE totalSupply

vars == << accounts, totalSupply >>

\* Helpers

\* Here f is a function of DOMAIN -> Int, S is the subset of DOMAIN to calculate the sum over
RECURSIVE Sum(_,_)
Sum(f,S) == IF S = {} THEN 0
            ELSE 
                LET x == CHOOSE x \in S : TRUE
                IN  f[x] + Sum(f, S \ {x})

\* Transitions  
    
Send(sender, receiver, denomination, amount) ==
    LET 
        senderBalance == accounts[sender][denomination] - amount  
        receiverBalance == accounts[receiver][denomination] + amount 
    IN 
    /\ sender /= receiver
    /\ accounts[sender][denomination] >= amount
    /\ accounts' = [accounts EXCEPT ![sender][denomination] = senderBalance, ![receiver][denomination] = receiverBalance]
    /\ UNCHANGED << totalSupply >>

\* Specification

Init == 
    /\ accounts = 
        (Acc1 :> (BTC :> 0 @@ ETH :> 1) @@ Acc2 :> (BTC :> 2 @@ ETH :> 3))
    /\ totalSupply = 
        (BTC :> 2 @@ ETH :> 4)

Next == 
    \/ \E sender \in AccountNames:
        \E denom \in CoinDenominations:
            \E receiver \in AccountNames:
                \E amt \in 0..accounts[sender][denom]:
                    /\ Send(sender, receiver, denom, amt)

Spec == Init /\ [][Next]_vars

\* Invariants

TypeOK == /\ accounts \in AccountType
          /\ totalSupply \in TotalSupplyType

TotalSupplyCorrect == 
    \A denom \in CoinDenominations:
        LET
            amountInAccounts == [acc \in AccountNames |-> accounts[acc][denom]]
        IN totalSupply[denom] = Sum(amountInAccounts, DOMAIN accounts)

NoOverdrafts == 
    \A acc \in AccountNames: 
        \A denom \in CoinDenominations:
            accounts[acc][denom] >= 0

\* Just a temporary debugging helper invariant
TEMP_SupplyDoesNotIncrease == 
    \A acc \in AccountNames: 
        \A denom \in CoinDenominations:
            accounts[acc][denom] < 5

=============================================================================
