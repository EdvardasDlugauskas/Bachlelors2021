-------------------------------- MODULE bank --------------------------------

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

\* Constants

CONSTANTS ETH, BTC, DOGE
CONSTANTS EscrowAcc, Acc1, Acc2, Acc3
CONSTANTS MAX_SUPPLY_HEIGHT, MAX_PACKET_COUNT_HEIGHT

ChainNames == {ETH, BTC, DOGE}
CoinDenominations == ChainNames

AccountNames == {EscrowAcc, Acc1, Acc2, Acc3}

MAX_PACKET_COUNT == 0..MAX_PACKET_COUNT_HEIGHT

MAX_SUPPLY == 0..MAX_SUPPLY_HEIGHT

GENESIS_SUPPLY == [c \in CoinDenominations |-> MAX_SUPPLY_HEIGHT]

\* Type

CoinType == [CoinDenominations -> MAX_SUPPLY]

AccountType == [AccountNames -> CoinType]

ChainType == [ChainNames -> AccountType]

ChannelNameType == {<<x, y>> \in {<<x, y>>: x, y \in ChainNames}: x /= y}

PacketType == [id: MAX_PACKET_COUNT, denom: CoinDenominations, amount: MAX_SUPPLY, sender: AccountNames, receiver: AccountNames]

ChannelType == [ChannelNameType -> SUBSET PacketType]

\* Vars

VARIABLE chains
VARIABLE channels
VARIABLE lastPacketId

vars == << chains, channels, lastPacketId >>

\* Helpers

NativeChainOf(denomination) == denomination

Pick(S) == CHOOSE s \in S : TRUE
RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == IF S = {} THEN value
                              ELSE LET s == Pick(S)
                              IN SetReduce(Op, S \ {s}, Op(s, value)) 

Sum(S) == LET _op(a, b) == a + b
          IN SetReduce(_op, S, 0)

\* Here f is a function of DOMAIN -> Int, S is the subset of DOMAIN to calculate the sum over
RECURSIVE SumDomain(_,_)
SumDomain(f,S) == IF S = {} THEN 0
            ELSE 
                LET x == Pick(S)
                IN  f[x] + SumDomain(f, S \ {x})

\* Transitions  

MintCoins(chain, receiver, denom, amount) ==
    /\ chains' = [chains EXCEPT 
        ![chain][receiver][denom] = chains[chain][receiver][denom] + amount]

BurnCoins(chain, sender, denom, amount) ==
    /\ chains' = [chains EXCEPT
        ![chain][sender][denom] = chains[chain][sender][denom] - amount]

LocalTransfer(chain, sender, receiver, denomination, amount) ==
    /\ chains' = [chains EXCEPT 
                    ![chain][sender][denomination] = chains[chain][sender][denomination] - amount, 
                    ![chain][receiver][denomination] = chains[chain][receiver][denomination] + amount]

ConditionalLocalTransfer(chain, sender, receiver, denomination, amount) ==
    /\ sender /= receiver
    /\ sender /= EscrowAcc
    /\ receiver /= EscrowAcc
    /\ amount > 0
    /\ chains[chain][sender][denomination] >= amount
    /\ LocalTransfer(NativeChainOf(denomination), sender, receiver, denomination, amount)

LocalTransferStep ==
    /\ \E chain \in ChainNames, sender, receiver \in AccountNames \ {EscrowAcc}, denomination \in CoinDenominations:
            /\  \E amount \in 0..chains[chain][sender][denomination]:
                ConditionalLocalTransfer(NativeChainOf(denomination), sender, receiver, denomination, amount)
    /\ UNCHANGED << channels, lastPacketId >>
    
 CreateOutgoingPacket(channel, sender, receiver, denomination, amount) ==
     /\ channel[1] /= channel[2]
     /\ LET
        sourceChain == channel[1]
        destChain == channel[2]
        packetId == lastPacketId + 1
        packet == [id |-> packetId, denom |-> denomination, amount |-> amount, sender |-> sender, receiver |-> receiver]
        isTokenSource == sourceChain = NativeChainOf(packet.denom)
        IN
        /\  IF isTokenSource
            THEN LocalTransfer(sourceChain, sender, EscrowAcc, denomination, amount)
            ELSE BurnCoins(sourceChain, sender, denomination, amount)
        /\ channels' = [channels EXCEPT ![channel] = (channels[channel] \union { packet })]
        /\ lastPacketId' = packetId

ConditionalCreateOutgoingPacket(channel, sender, receiver, denomination, amount) ==
    /\ sender /= receiver
    /\ sender /= EscrowAcc
    /\ receiver /= EscrowAcc
    /\ amount > 0
    /\ chains[channel[1]][sender][denomination] >= amount
    /\ CreateOutgoingPacket(channel, sender, receiver, denomination, amount)

CreateOutgoingPacketStep ==
    /\ lastPacketId < MAX_PACKET_COUNT_HEIGHT
    /\ \E channel \in ChannelNameType, sender, receiver \in AccountNames \ {EscrowAcc}, denom \in CoinDenominations:
        \E amt \in 0..chains[channel[1]][sender][denom]:
            /\ ConditionalCreateOutgoingPacket(channel, sender, receiver, denom, amt)
    /\ UNCHANGED << >>

RefundTokens(channel, packet) ==
    /\ LET 
        sourceChain == channel[1]
        destinationChain == channel[2]
        isTokenSource == sourceChain = NativeChainOf(packet.denom)
        IN
        /\  IF isTokenSource
            THEN LocalTransfer(sourceChain, EscrowAcc, packet.sender, packet.denom, packet.amount)
            ELSE MintCoins(sourceChain, packet.sender, packet.denom, packet.amount)
        /\ channels' = [channels EXCEPT ![channel] = channels[channel] \ {packet}]

ReceivePacket(channel, packet) ==
    /\ LET 
        sourceChain == channel[1]
        destinationChain == channel[2]
        isTokenSource == destinationChain = NativeChainOf(packet.denom)
        IN
        /\  IF isTokenSource
            THEN LocalTransfer(destinationChain, EscrowAcc, packet.receiver, packet.denom, packet.amount)
            ELSE MintCoins(destinationChain, packet.receiver, packet.denom, packet.amount)
        /\ channels' = [channels EXCEPT ![channel] = channels[channel] \ {packet}]

ReceivePacketStep == 
    /\ \E channel \in ChannelNameType:
        /\ \E packet \in channels[channel]:
            /\ ReceivePacket(channel, packet)
    /\ UNCHANGED << lastPacketId >>

TimeoutPacketStep ==
    \E channel \in ChannelNameType:
        \E packet \in channels[channel]:
            /\ RefundTokens(channel, packet)
    /\ UNCHANGED << lastPacketId >>

FailAcknowledgePacketStep ==
    \E channel \in ChannelNameType:
        \E packet \in channels[channel]:
            /\ RefundTokens(channel, packet)
    /\ UNCHANGED << lastPacketId >>

\* Specification

Init ==
    \* Pre-configured state for MAX_SUPPLY_HEIGHT == 1
    /\ chains = (
        BTC :> (Acc1 :> (BTC :> 1 @@ ETH :> 0 @@ DOGE :> 0) @@ Acc2 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0) @@ Acc3 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0) @@ EscrowAcc :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0)) @@
        ETH :> (Acc1 :> (BTC :> 0 @@ ETH :> 1 @@ DOGE :> 0) @@ Acc2 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0) @@ Acc3 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0) @@ EscrowAcc :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0)) @@
        DOGE :> (Acc1 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 1) @@ Acc2 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0) @@ Acc3 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0) @@ EscrowAcc :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0)) 
        )
    /\ channels = (<<BTC, ETH>> :> {} @@ <<ETH, BTC>> :> {} @@ <<ETH, DOGE>> :> {} @@ <<BTC, DOGE>> :> {} @@ <<DOGE, ETH>> :> {} @@ <<DOGE, BTC>> :> {})
    /\ lastPacketId = 0

    \* \* Pre-configured state for MAX_SUPPLY_HEIGHT == 2
    \* /\ chains = (
    \*     \* BTC escrow should have at least the "sum of all non-BTC chain BTC balances" tokens
    \*     BTC :> (Acc1 :> (BTC :> 0 @@ ETH :> 1 @@ DOGE :> 0) @@ Acc2 :> (BTC :> 0 @@ ETH :> 1 @@ DOGE :> 0) @@ Acc3 :> (BTC :> 1 @@ ETH :> 0 @@ DOGE :> 0) @@ EscrowAcc :> (BTC :> 1 @@ ETH :> 0 @@ DOGE :> 0)) @@
    \*     ETH :> (Acc1 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0) @@ Acc2 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0) @@ Acc3 :> (BTC :> 1 @@ ETH :> 0 @@ DOGE :> 0) @@ EscrowAcc :> (BTC :> 0 @@ ETH :> 2 @@ DOGE :> 0)) @@
    \*     DOGE :> (Acc1 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 2) @@ Acc2 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0) @@ Acc3 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0) @@ EscrowAcc :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0)) 
    \*     )
    \* /\ channels = (<<BTC, ETH>> :> {} @@ <<ETH, BTC>> :> {} @@ <<ETH, DOGE>> :> {} @@ <<BTC, DOGE>> :> {} @@ <<DOGE, ETH>> :> {} @@ <<DOGE, BTC>> :> {})
    \* /\ lastPacketId = 0

    \* \* Pre-configured state for MAX_PACKET_COUNT_HEIGHT == 3 and MAX_SUPPLY_HEIGHT == 4
    \* /\ chains = (
    \*     BTC :> (Acc1 :> (BTC :> 1 @@ ETH :> 1 @@ DOGE :> 0) @@ Acc2 :> (BTC :> 0 @@ ETH :> 1 @@ DOGE :> 0) @@ Acc3 :> (BTC :> 1 @@ ETH :> 0 @@ DOGE :> 0) @@ EscrowAcc :> (BTC :> 2 @@ ETH :> 0 @@ DOGE :> 0)) @@
    \*     ETH :> (Acc1 :> (BTC :> 1 @@ ETH :> 1 @@ DOGE :> 0) @@ Acc2 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0) @@ Acc3 :> (BTC :> 1 @@ ETH :> 1 @@ DOGE :> 0) @@ EscrowAcc :> (BTC :> 0 @@ ETH :> 2 @@ DOGE :> 0)) @@
    \*     DOGE :> (Acc1 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 3) @@ Acc2 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 1) @@ Acc3 :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0) @@ EscrowAcc :> (BTC :> 0 @@ ETH :> 0 @@ DOGE :> 0)) 
    \*     )
    \* /\ channels = (<<BTC, ETH>> :> {} @@ <<ETH, BTC>> :> {} @@ <<ETH, DOGE>> :> {} @@ <<BTC, DOGE>> :> {} @@ <<DOGE, ETH>> :> {} @@ <<DOGE, BTC>> :> {})
    \* /\ lastPacketId = 0

    \* /\ \E c \in ChainType, chan \in ChannelType:
    \*     /\ chains = c
    \*     /\ \A denom \in CoinDenominations:
    \*         /\ SumDomain([acc \in AccountNames |-> c[NativeChainOf(denom)][acc][denom]], DOMAIN c[NativeChainOf(denom)]) = GENESIS_SUPPLY[denom]

    \*     /\ \A channelName \in ChannelNameType: chan[channelName] = {}
    \*     /\ channels = chan
    \*     /\ lastPacketId = 0

Next == 
    \/ LocalTransferStep
    \/ CreateOutgoingPacketStep
    \/ TimeoutPacketStep
    \/ FailAcknowledgePacketStep 
    \/ ReceivePacketStep

Spec == Init /\ [][Next]_vars 
             /\ WF_vars(ReceivePacketStep)

\* Invariants and properties

TypeOK == 
    /\ chains \in ChainType
    /\ channels \in ChannelType
    /\ lastPacketId \in Int

TotalSupplyCorrect == 
    /\ \A denom \in CoinDenominations:
        /\ SumDomain([acc \in AccountNames |-> chains[denom][acc][denom]], DOMAIN chains[denom]) = MAX_SUPPLY_HEIGHT

NoOverdrafts == 
    \A chainName \in ChainNames, acc \in AccountNames, denom \in CoinDenominations: 
        chains[chainName][acc][denom] >= 0

EscrowHasEnoughTokensToCoverAllIncomingNativePackets ==
    \A channel \in ChannelNameType:
        LET
            receiverDenom == channel[2]
            receiverChainEscrow == chains[NativeChainOf(receiverDenom)][EscrowAcc]
            incomingNativeCoinPackets == {packet \in channels[channel]: packet.denom = receiverDenom}
            minimumEscrowAmount == Sum({p.amount: p \in incomingNativeCoinPackets})
        IN
            receiverChainEscrow[receiverDenom] >= minimumEscrowAmount

SentPacketsArriveOrGetDropped ==
    \A channel \in ChannelNameType: \A packet \in PacketType: 
        packet \in channels[channel] ~> packet \notin channels[channel]

=============================================================================
