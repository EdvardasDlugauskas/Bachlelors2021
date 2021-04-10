-------------------------------- MODULE bank --------------------------------


EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

\* Constants

CONSTANTS ETH, BTC, DOGE
CONSTANTS EscrowAcc, Acc1, Acc2, Acc3, Acc4, Acc5

ChainNames == {ETH, BTC} \*, DOGE}
CoinDenominations == ChainNames

AccountNames == {EscrowAcc, Acc1} \*Acc2} \*, Acc3, Acc4, Acc5}

MAX_INT_HEIGHT == 1 \* TODO: change
MAX_INT == 0..MAX_INT_HEIGHT
GENESIS_SUPPLY == [c \in CoinDenominations |-> MAX_INT_HEIGHT]

\* Type

CoinType == [CoinDenominations -> MAX_INT]

AccountType == [AccountNames -> CoinType]

TotalSupplyType == [CoinDenominations -> MAX_INT]

ChainType == [ChainNames -> AccountType]

ChannelNameType == {<<x, y>> \in {<<x, y>>: x, y \in ChainNames}: x /= y}

PacketType == [id: MAX_INT, denom: CoinDenominations, amount: MAX_INT, sender: AccountNames, receiver: AccountNames]

ChannelType == [ChannelNameType -> SUBSET PacketType]

\* Vars

VARIABLE chains
VARIABLE totalSupply
VARIABLE channels
VARIABLE lastPacketId

vars == << chains, channels, totalSupply, lastPacketId >>

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

LocalTransferStep ==
    /\ \E chain \in ChainNames, sender, receiver \in AccountNames, denom \in CoinDenominations:
            \E amt \in 0..chains[chain][sender][denom]:
                /\ LocalTransfer(sender, receiver, denom, amt)
    /\ UNCHANGED << totalSupply, channels, lastPacketId >>
    
 CreateOutgoingPacket(channel, sender, receiver, denomination, amount) ==
     /\ lastPacketId < MAX_INT_HEIGHT
     /\ channel[1] /= channel[2]
     /\ LET
        sourceChain == channel[1]
        destChain == channel[2]
        packetId == lastPacketId + 1
        packet == [id |-> packetId, denom |-> denomination, amount |-> amount, sender |-> sender, receiver |-> receiver]
        IN
        /\ chains[sourceChain][sender][denomination] >= amount
        /\ LocalTransfer(sender, EscrowAcc, denomination, amount)
        /\ channels' = [channels EXCEPT ![channel] = (channels[channel] \union { packet })]
        /\ lastPacketId' = packetId

CreateOutgoingPacketStep ==
    /\ \E channel \in ChannelNameType, chain \in ChainNames, sender, receiver \in AccountNames, denom \in CoinDenominations:
        \E amt \in 0..chains[chain][sender][denom]:
            /\ CreateOutgoingPacket(channel, sender, receiver, denom, amt)
    /\ UNCHANGED totalSupply

\* Specification

Init ==
    /\ \E c \in ChainType, chan \in ChannelType:
        /\ chains = c
        /\ \A denom \in CoinDenominations:
            /\ Sum([acc \in AccountNames |-> c[denom][acc][denom]], DOMAIN c[denom]) = GENESIS_SUPPLY[denom]

        /\ \A channelName \in ChannelNameType: chan[channelName] = {}
        /\ channels = chan

        /\ totalSupply = GENESIS_SUPPLY
        /\ lastPacketId = 0

Next == 
    /\  \/ LocalTransferStep
        \/ CreateOutgoingPacketStep

Spec == Init /\ [][Next]_vars

\* Invariants

TypeOK == /\ chains \in ChainType
          /\ totalSupply \in TotalSupplyType
          /\ channels \in ChannelType
          /\ lastPacketId \in Int

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
