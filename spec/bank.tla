-------------------------------- MODULE bank --------------------------------


EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

\* Constants

CONSTANTS ETH, BTC, DOGE
CONSTANTS EscrowAcc, Acc1, Acc2, Acc3, Acc4, Acc5

ChainNames == {ETH, BTC} \*, DOGE}
CoinDenominations == ChainNames

AccountNames == {EscrowAcc, Acc1, Acc2, Acc3} \*, Acc4, Acc5}

MAX_PACKET_COUNT_HEIGHT == 3
MAX_PACKET_COUNT == 0..MAX_PACKET_COUNT_HEIGHT

MAX_SUPPLY_HEIGHT == 15
MAX_SUPPLY == 0..MAX_SUPPLY_HEIGHT
GENESIS_SUPPLY == [c \in CoinDenominations |-> MAX_SUPPLY_HEIGHT]

MAX_INT_HEIGHT == 1 \* TODO: change
MAX_INT == 0..MAX_INT_HEIGHT

\* Type

CoinType == [CoinDenominations -> Int] \* MAX_SUPPLY

AccountType == [AccountNames -> CoinType]

TotalSupplyType == [CoinDenominations -> Int] \* MAX_SUPPLY

ChainType == [ChainNames -> AccountType]

ChannelNameType == {<<x, y>> \in {<<x, y>>: x, y \in ChainNames}: x /= y}

PacketType == [id: MAX_PACKET_COUNT, denom: CoinDenominations, amount: MAX_SUPPLY, sender: AccountNames, receiver: AccountNames]

ChannelType == [ChannelNameType -> SUBSET PacketType]

\* Vars

VARIABLE chains
VARIABLE totalSupply
VARIABLE channels
VARIABLE lastPacketId

vars == << chains, channels, totalSupply, lastPacketId >>

\* Helpers

NativeChainOf(chain) == chain

\* Here f is a function of DOMAIN -> Int, S is the subset of DOMAIN to calculate the sum over
RECURSIVE Sum(_,_)
Sum(f,S) == IF S = {} THEN 0
            ELSE 
                LET x == CHOOSE x \in S : TRUE
                IN  f[x] + Sum(f, S \ {x})

\* Transitions  

LocalTransfer(chain, sender, receiver, denomination, amount) ==
    /\  LET 
        senderBalance == chains[chain][sender][denomination]
        newSenderBalance == senderBalance - amount  
        receiverBalance == chains[chain][receiver][denomination]
        newReceiverBalance == receiverBalance + amount 
        IN 
        /\ senderBalance >= amount
        /\ chains' = [chains EXCEPT 
                        ![chain][sender][denomination] = newSenderBalance, 
                        ![chain][receiver][denomination] = newReceiverBalance]

LocalTransferStep ==
    /\ \E chain \in ChainNames, sender, receiver \in AccountNames \ {EscrowAcc}, denom \in CoinDenominations:
            \E amt \in 0..chains[chain][sender][denom]:
                /\ sender /= receiver
                /\ sender /= EscrowAcc
                /\ amt > 0
                /\ LocalTransfer(NativeChainOf(denom), sender, receiver, denom, amt)
    /\ UNCHANGED << totalSupply, channels, lastPacketId >>
    
 CreateOutgoingPacket(channel, sender, receiver, denomination, amount) ==
     /\ channel[1] /= channel[2]
     /\ LET
        sourceChain == channel[1]
        destChain == channel[2]
        packetId == lastPacketId + 1
        packet == [id |-> packetId, denom |-> denomination, amount |-> amount, sender |-> sender, receiver |-> receiver]
        IN
        /\ chains[sourceChain][sender][denomination] >= amount
        /\ LocalTransfer(sourceChain, sender, EscrowAcc, denomination, amount)
        /\ channels' = [channels EXCEPT ![channel] = (channels[channel] \union { packet })]
        /\ lastPacketId' = packetId

CreateOutgoingPacketStep ==
    /\ lastPacketId < MAX_PACKET_COUNT_HEIGHT
    /\ \E channel \in ChannelNameType, chain \in ChainNames, sender, receiver \in AccountNames \ {EscrowAcc}, denom \in CoinDenominations:
        \E amt \in 0..chains[chain][sender][denom]:
            /\ sender /= receiver
            /\ amt > 0
            /\ CreateOutgoingPacket(channel, sender, receiver, denom, amt)
    /\ UNCHANGED totalSupply

\* TODO: mint if chain is receiving it's own denomination
RefundTokens(packet, channel) ==
    /\ LET 
        source == channel[1]
        refundAmount == packet.amount
        refundee == packet.sender
        denomination == packet.denom
        IN
        /\ chains' = [chains EXCEPT 
                        ![source][refundee][denomination] = chains[source][refundee][denomination] + refundAmount,
                        ![source][EscrowAcc][denomination] = chains[source][EscrowAcc][denomination] - refundAmount]
        /\ channels' = [channels EXCEPT ![channel] = channels[channel] \ {packet}]


TimeoutPacketStep ==
    \E channel \in ChannelNameType:
        \E packet \in channels[channel]:
            RefundTokens(packet, channel)
    /\ UNCHANGED << totalSupply, lastPacketId >>

FailAcknowledgePacketStep ==
    \E channel \in ChannelNameType:
        \E packet \in channels[channel]:
            RefundTokens(packet, channel)
    /\ UNCHANGED << totalSupply, lastPacketId >>

\* Specification

Init ==
    /\ chains = (
        BTC :> (Acc1 :> (BTC :> 1 @@ ETH :> 1) @@ Acc2 :> (BTC :> 0 @@ ETH :> 1) @@ Acc3 :> (BTC :> 1 @@ ETH :> 1) @@ EscrowAcc :> (BTC :> 1 @@ ETH :> 1)) @@
        ETH :> (Acc1 :> (BTC :> 0 @@ ETH :> 1) @@ Acc2 :> (BTC :> 1 @@ ETH :> 1) @@ Acc3 :> (BTC :> 1 @@ ETH :> 1) @@ EscrowAcc :> (BTC :> 0 @@ ETH :> 0))
        )
    /\ channels = (<<BTC, ETH>> :> {} @@ <<ETH, BTC>> :> {})
    /\ totalSupply = GENESIS_SUPPLY
    /\ lastPacketId = 0

    \* /\ \E c \in ChainType, chan \in ChannelType:
    \*     /\ chains = c
    \*     /\ \A denom \in CoinDenominations:
    \*         /\ Sum([acc \in AccountNames |-> c[denom][acc][denom]], DOMAIN c[denom]) = GENESIS_SUPPLY[denom]

    \*     /\ \A channelName \in ChannelNameType: chan[channelName] = {}
    \*     /\ channels = chan

    \*     /\ totalSupply = GENESIS_SUPPLY
    \*     /\ lastPacketId = 0

Next == 
    /\  \/ LocalTransferStep
        \/ CreateOutgoingPacketStep
        \/ TimeoutPacketStep
        \/ FailAcknowledgePacketStep 

Spec == Init /\ [][Next]_vars

\* Invariants

TypeOK == 
    /\ chains \in ChainType
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
