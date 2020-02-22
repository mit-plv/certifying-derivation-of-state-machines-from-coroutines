Require Import List.
Require Import Inhabit Foldable ClConv.
Import ListNotations.

Parameter String : Set.
Parameter ByteString : Set.

Inductive Group := P256 | P384 | P521 | X25519.

Inductive PskMode := pskModePlain | PskModeDHE.

Inductive SignatureScheme :=
  PKCS1WithSHA256
| PKCS1WithSHA384
| PKCS1WithSHA512
| PSSWithSHA256
| PSSWithSHA384
| PSSWithSHA512
| ECDSAWithP256AndSHA256
| ECDSAWithP384AndSHA384
| ECDSAWithP512AndSHA512
| Ed25519
| PKCS1WithSHA1
| ECDSAWithSHA1.

Scheme Equality for Group.
Scheme Equality for PskMode.
Scheme Equality for SignatureScheme.


Record KeyShare :=
  { KSgroup : Group;
    KSdata : ByteString
  }.

Parameter ExtensionRaw : Set.
Parameter Session : Set.
Parameter CipherID : Set.

Record ClientHelloMsg :=
  {
    chSession : Session;
    chExtension : list ExtensionRaw;
    chCiphers : list CipherID
  }.

Ltac nth_of_tuple' p n flag :=
  lazymatch n with
  | O =>
    lazymatch flag with
    | true => exact p
    | false => exact (snd p)
    end
  | S ?n' => nth_of_tuple' (fst p) n' flag
  end.

Ltac nth_of_tuple p n :=
  let ty := type of p in
  let rec aux ty :=
      lazymatch ty with
      | ?ty' * _ => let v := aux ty' in constr:(S v)
      | _ => O
      end
  in
  let m := aux ty in
  let n' := (eval simpl in (m - n)) in
  lazymatch n with
  | O => nth_of_tuple' p n' true
  | _ => nth_of_tuple' p n' false
  end.

Notation "p ._( n )" :=
  ltac:(nth_of_tuple p n)
         (at level 0, only parsing).

Parameter ServerParams : Set.
Parameter Context : Set.

Parameter serverGroups : list Group.

Fixpoint findKeyShare ks gs :=
  match gs with
  | [] => None
  | g::gs' =>
    match find (fun k => Group_beq (KSgroup k) g) ks with
    | Some k => Some k
    | None => findKeyShare ks gs'
    end
  end.

Definition intersect (xs ys : list Group) :=
  filter (fun x => if in_dec Group_eq_dec x ys then true else false) xs.

Parameter extension_KeyShare : list ExtensionRaw -> option (list KeyShare).
Parameter extension_NegotiatedGroups : list ExtensionRaw -> list Group.
Parameter word32 : Set.

Inductive PskIdentity := Build_PskIdentity : ByteString -> word32 -> PskIdentity.

Inductive PreSharedKey :=
| PreSharedKeyClientHello : list PskIdentity -> list ByteString -> PreSharedKey
| PreSharedKeyServerHello : nat -> PreSharedKey.

Parameter extension_PreSharedKey : list ExtensionRaw -> option PreSharedKey.
Parameter Handshake13 : Set.
Parameter Packet13 : Set.

Inductive eff_tls := recvClientHello | getRandomBytes | sendPacket.

Definition args_tls ef :=
  match ef with
  | recvClientHello => unit
  | getRandomBytes => nat
  | sendPacket => Packet13
  end.

Definition rets_tls ef :=
  match ef with
  | recvClientHello => ClientHelloMsg
  | getRandomBytes => ByteString
  | sendPacket => unit
  end.

Definition lift_tls A B(e : eff_tls)(a : rets_tls e -> A + option B) e0
  : rets_tls e0 -> A + option B :=
  match
  e as e1
  return ((rets_tls e1 -> A + option B) -> rets_tls e0 -> A + option B)
  with
  | recvClientHello =>
    fun a0 : rets_tls recvClientHello -> A + option B =>
      match e0 as e1 return (rets_tls e1 -> A + option B) with
      | recvClientHello => a0
      | _ => fun _ => inr None
      end
  | getRandomBytes =>
    fun a0 : rets_tls getRandomBytes -> A + option B =>
      match e0 as e1 return (rets_tls e1 -> A + option B) with
      | getRandomBytes => a0
      | _ => fun _ => inr None
      end
  | sendPacket =>
    fun a0 : rets_tls sendPacket -> A + option B =>
      match e0 as e1 return (rets_tls e1 -> A + option B) with
      | sendPacket => a0
      | _ => fun _ => inr None
      end
  end a.

Instance eff_tls_is_eff : is_eff eff_tls :=
  { args := args_tls;
    rets := rets_tls;
    lift_eff := lift_tls }.

Notation "ch <-recvClientHello ctx ; p" :=
  (@Eff eff_tls args_tls rets_tls _ recvClientHello ctx (fun ch => p))
    (at level 100, right associativity).

Notation "b <-getRandomBytes n ; p" :=
  (@Eff eff_tls args_tls rets_tls _ getRandomBytes n (fun b => p))
    (at level 100, right associativity).

Notation "'sendPkt' b ; p" :=
  (@Eff eff_tls args_tls rets_tls _ sendPacket b (fun _ => p))
    (at level 200, right associativity).

Definition option_beq {A} (A_beq : A -> A -> bool) o1 o2 :=
  match o1, o2 with
  | None, None => true
  | Some a1, Some a2 => A_beq a1 a2
  | _,_ => false
  end.

Parameter Hash : Set.
Parameter HostName : Set.
Parameter ctxGetClientSNI : Context -> option HostName.
Parameter ctxGetNegotiatedProtocol : Context -> option ByteString.
Parameter Cipher : Set.
Parameter CipherID_beq : CipherID -> CipherID -> bool.
Parameter SessionData : Set.
Parameter sessionCipher : SessionData -> CipherID.
Parameter cipherID : Cipher -> CipherID.
Parameter serverSupportedCiphers : ServerParams -> list Cipher.
Parameter Hash_beq : Hash -> Hash -> bool.
Parameter cipherHash : Cipher -> Hash.
Parameter Version : Set.
Parameter Version_beq : Version -> Version -> bool.
Parameter sessionVersion : SessionData -> Version.
Parameter ByteString_beq : ByteString -> ByteString -> bool.
Parameter sessionALPN : SessionData -> option ByteString.

Open Scope bool_scope.

Definition checkSessionEquality ctx sparams chosenVersion usedCipher sdata :=
  let msni := ctxGetClientSNI ctx in
  let malpn := ctxGetNegotiatedProtocol ctx in
  let isSameCipher := CipherID_beq (sessionCipher sdata) (cipherID usedCipher) in
  let ciphers := serverSupportedCiphers sparams in
  let isSameKDF :=
      match find (fun c => CipherID_beq (cipherID c) (sessionCipher sdata)) ciphers with
      | Some c => Hash_beq (cipherHash c) (cipherHash usedCipher)
      | Nothing => false
      end
  in
  let isSameVersion := Version_beq chosenVersion (sessionVersion sdata) in
  let isSameALPN := option_beq ByteString_beq (sessionALPN sdata) malpn in
  let is0RTTvalid := isSameVersion && isSameCipher && isSameALPN in
  (isSameKDF, is0RTTvalid).

Parameter PskKexMode : Set.
Parameter PSK_DHE_KE : PskKexMode.
Parameter extension_PskKeyExchangeModes : list ExtensionRaw -> option (list PskKexMode).
Parameter PskKexMode_eq_dec : forall x y : PskKexMode, {x=y}+{x<>y}.
Parameter zero : ByteString.
Parameter Blength : ByteString -> nat.
Parameter SessionManager : Set.
Parameter serverSharedSessionManager : ServerParams -> SessionManager.
Parameter sessionResume : SessionManager -> ByteString -> option SessionData.
Parameter sessionResumeOnlyOnce : SessionManager -> ByteString -> option SessionData.
Parameter sessionSecret : SessionData -> ByteString.
Definition sum_nat xs := fold_left Nat.add xs 0.

Definition choosePSK (rtt0:bool) ctx sparams chosenVersion usedCipher exts :=
  match extension_PreSharedKey exts with
  | Some (PreSharedKeyClientHello (Build_PskIdentity sessionId obfAge::_) (bnd::_ as bnds)) =>
    match extension_PskKeyExchangeModes exts with
    | None => (zero, None, false)
    | Some dhModes =>
      if in_dec PskKexMode_eq_dec PSK_DHE_KE dhModes then
        let len := (sum_nat (map (fun x => Blength x + 1) bnds) + 2)%nat in
        let mgr := serverSharedSessionManager sparams in
        let msdata :=
            if rtt0 then sessionResumeOnlyOnce mgr sessionId
            else sessionResume mgr sessionId
        in
          match msdata with
          | Some sdata =>
            let psk := sessionSecret sdata in
            let validity := checkSessionEquality ctx sparams chosenVersion usedCipher sdata in
            if (fst validity) then
              (psk, Some (bnd,0,len), snd validity)
            else
              (zero, None, false)
          | Nothing => (zero, None, false)
          end
      else
        (zero, None, false)
    end
  | _ => (zero, None, false)
  end.

Parameter extensionEncode_KeyShare : KeyShare -> ByteString.
Parameter extensionEncode_SupportedVersions : Version -> ByteString.
Parameter TLS13 : Version.
Parameter extensionRaw_KeyShare : ByteString -> ExtensionRaw.
Parameter extensionRaw_SupportedVersions : ByteString -> ExtensionRaw.
Parameter handshake13 : list Handshake13 -> Packet13.
Parameter serverHello13 : ByteString -> Session -> CipherID -> list ExtensionRaw -> Handshake13.

Definition doHandshake :=
  ch <-recvClientHello tt;
    let opt := extension_KeyShare ch.(chExtension) in
    match opt with
    | None => Return None
    | Some keyShares =>
      let oks := findKeyShare keyShares serverGroups in
      match oks with
      | None => Return None
      | Some keyShare =>
        (* sendServerHello *)
        let serverKeyShare := extensionEncode_KeyShare keyShare in
        let selectedVersion := extensionEncode_SupportedVersions TLS13 in
        let extensions' := [ extensionRaw_KeyShare serverKeyShare;
                             extensionRaw_SupportedVersions selectedVersion ]
        in
        srand <-getRandomBytes 32;
          match hd_error (chCiphers ch) with
          | None => Return None
          | Some cipher =>
            srand <-getRandomBytes 32;
            sendPkt (handshake13 [serverHello13 srand (chSession ch) cipher extensions']);
              Return (Some tt)
          end
      end
    end.

Definition doHandshake_derive :
  { state & { step &
                { init | @equiv _ _ _ _ state step init doHandshake }}}.
Proof.
  do 3 eexists.
  unfold doHandshake.
  derive' tt.
Defined.

Definition doHandshake_step := Eval cbv [projT1 projT2 doHandshake doHandshake_derive] in (projT1 (projT2 doHandshake_derive)).

Definition pickKeyShare :=
  ch <-recvClientHello tt;
    match extension_KeyShare ch.(chExtension) with
    | None => Return None
    | Some keyShares =>
      match findKeyShare keyShares (serverGroups) with
      | None =>
        (* helloRetryRequest *)
        let clientGroups := extension_NegotiatedGroups ch.(chExtension) in
        let possibleGroups := intersect (serverGroups) clientGroups in
        match hd_error possibleGroups with
        | None => Return None
        | Some g => 
          ch' <-recvClientHello tt;
            match extension_KeyShare ch'.(chExtension) with
            | None => Return None
            | Some keyShares =>
              match findKeyShare keyShares (serverGroups ) with
              | None => Return None
              | Some keyShare => Return (Some (ch', keyShare))
              end
            end
        end
        (* helloRetryRequest end *)
      | Some keyShare => Return (Some (ch, keyShare))
      end
    end.
(*
Definition pickKeyShare_derive :
  { state & { step & forall ctx,
                { init | @equiv _ _ _ _ state step init (pickKeyShare ctx) }}}.
Proof.
  do 3 eexists.
  unfold pickKeyShare.
  derive' (tt,ctx).
Defined.

Definition pickKeyShare_step := Eval cbv [projT1 projT2 pickKeyShare pickKeyShare_derive] in (fun ctx => projT1 (projT2 pickKeyShare_derive) ctx).
*)


Extract Inductive unit => "()" [ "()" ].
Extract Inductive list => "([])" ["[]" "(:)"].
Extract Inductive nat => "Int" ["0" "(Prelude.+) 1"] "(\fO fS n -> if n==0 then fO () else fS (n Prelude.- 1))".
Extract Inductive bool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"].
Extract Inductive sumbool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"].
Extract Inductive prod => "(,)"  [ "(,)" ].
Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].
Extract Inductive option => "GHC.Base.Maybe" ["GHC.Base.Just" "GHC.Base.Nothing"].
Extract Inductive Group => "T.Group" ["T.P256" "T.P384" "T.P521" "T.X25519"].
Extract Inductive KeyShare => "I.KeyShareEntry" ["I.KeyShareEntry"].
Extract Constant Group_eq_dec => "(GHC.Base.==)".
Extract Constant Group_beq => "(GHC.Base.==)".
Extract Constant Context => "T.Context".
Extract Constant ExtensionRaw => "I.ExtensionRaw".
Extract Constant Session => "I.Session".
Extract Constant CipherID => "T.CipherID".
Extract Constant Handshake13 => "I.Handshake13".
Extract Constant Packet13 => "I.Packet13".
Extract Constant ByteString => "B.ByteString".
Extract Constant extensionEncode_KeyShare => "(\ks -> I.extensionEncode (I.KeyShareServerHello ks))".
Extract Constant extensionEncode_SupportedVersions =>
"(\v -> I.extensionEncode (I.SupportedVersionsServerHello v))".
Extract Constant Version => "T.Version".
Extract Constant TLS13 => "T.TLS13".
Extract Constant extensionRaw_KeyShare => "I.ExtensionRaw I.extensionID_KeyShare".
Extract Constant extensionRaw_SupportedVersions =>
"I.ExtensionRaw I.extensionID_SupportedVersions".
Extract Constant handshake13 => "I.Handshake13".
Extract Constant serverHello13 => "(\b -> I.ServerHello13 (I.ServerRandom {I.unServerRandom = b}))".

Extract Constant extension_KeyShare =>
"(\exts -> case Helper.extensionLookup I.extensionID_KeyShare exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.KeyShareClientHello kses) -> GHC.Base.return kses})".
Extract Constant serverGroups => "Helper.serverGroups".

(*
Extract Constant extension_KeyShare => "Helper.extension_KeyShare".
Extract Constant extension_NegotiatedGroups => "Helper.extension_NegotiatedGroups".
Extract Constant serverGroups => "Helper.serverGroups".
Extract Inductive KeyShare => "Helper.KeyShare" ["Helper.Build_KeyShare"].
 *)

Require Extraction.
Extraction Language Haskell.

Extraction "TLS.hs" doHandshake_step.
