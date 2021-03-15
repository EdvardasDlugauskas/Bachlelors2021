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

\* Vars

VARIABLE accounts

vars == << accounts >>

\* Transitions

\* Increment(acc, denom) == 
\*     LET newValue == accounts[acc][denom] + 1 IN 
\*     /\ accounts' = [accounts EXCEPT ![acc][denom] = newValue]
\*     /\ UNCHANGED << >>
    
    
Send(sender, receiver, denomination, amount) ==
    LET 
        senderBalance == accounts[sender][denomination] - amount  
        receiverBalance == accounts[receiver][denomination] + amount 
    IN 
    /\ sender /= receiver
    /\ accounts[sender][denomination] >= amount
    /\ accounts' = [accounts EXCEPT ![sender][denomination] = senderBalance, ![receiver][denomination] = receiverBalance]

\* Specification

Init == 
    /\ accounts = 
        (Acc1 :> (BTC :> 0 @@ ETH :> 1) @@ Acc2 :> (BTC :> 2 @@ ETH :> 3))

Next == 
    \/ \E sender \in AccountNames:
        \E denom \in CoinDenominations:
            \E receiver \in AccountNames:
                \E amt \in 0..accounts[sender][denom]:
                    /\ Send(sender, receiver, denom, amt)

Spec == Init /\ [][Next]_vars

\* Invariants

TypeOK == accounts \in AccountType

\* Just a debugging helper invariant
SupplyDoesNotIncrease == 
    \A acc \in AccountNames: 
        \A denom \in CoinDenominations:
            accounts[acc][denom] < 5

NoOverdrafts == 
    \A acc \in AccountNames: 
        \A denom \in CoinDenominations:
            accounts[acc][denom] >= 0

=============================================================================
