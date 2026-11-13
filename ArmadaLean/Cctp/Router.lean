-- ABOUTME: A CCTP hook router's state: the Circle addresses its constructor fixed, possibly swapped by a deployer.
-- ABOUTME: Anyone may call a router; its relay step (a later commit) receives a message and dispatches the pool hook.
/-
  ArmadaLean.Cctp.Router — the state of one `CCTPHookRouter`.

  Design record: model sheet v2.1 §4.4. A router stores the MessageTransmitter and the
  TokenMessenger its constructor received, immutably (CCTPHookRouter.sol:35-47). The
  constructor takes them in the order (MessageTransmitter, TokenMessenger)
  (CCTPHookRouter.sol:40), the opposite of the pool's `initialize`; a router deployed with
  the two swapped is a reachable configuration (finding N-1, re-check RC2-14). Any address
  may deploy a router, so a chain may hold several.
-/
import ArmadaLean.Cctp.Types

namespace ArmadaLean.Cctp

/-- One hook router (CCTPHookRouter.sol:35-47): its own address and the two Circle
    addresses its constructor stored. `relayWithHook` checks that a message's envelope
    recipient is `tokenMessenger` (CCTPHookRouter.sol:62-65) and calls
    `receiveMessage` on `messageTransmitter` (CCTPHookRouter.sol:68). -/
structure RouterState where
  self : Term
  messageTransmitter : Term
  tokenMessenger : Term
  deriving DecidableEq

end ArmadaLean.Cctp
