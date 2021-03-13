-------------------------------- MODULE bank --------------------------------


EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

\* Constants

\* Vars

VARIABLE supply

vars == << supply >>

\* Transitions

MintCoins(amt) == 
    /\ supply' = supply + amt
    /\ UNCHANGED << >>
    
BurnCoins(amt) == 
    /\ supply >= amt
    /\ supply' = supply - amt
    /\ UNCHANGED << >> 
    
    
\* Specification

Init == 
    /\ supply = 0

Next == 
    \/ MintCoins(RandomElement(1..10))
    \/ BurnCoins(RandomElement(1..10))

Spec == Init /\[][Next]_vars

\* Invariants

TypeOK == supply \in Nat

SupplyIsNonNegative == 
    /\ supply >= 0 


=============================================================================
