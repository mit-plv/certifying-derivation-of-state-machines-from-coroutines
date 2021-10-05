Require Import List FunctionalExtensionality.
Require String.
Require Import Inhabit Foldable ClConv.
Import ListNotations.
Import String.StringSyntax.
Open Scope string_scope.

Parameter ByteString : Set.

Inductive Group := P256 | P384 | P521 | X25519.

Scheme Equality for Group.

Record KeyShare :=
  { ksGroup : Group;
    ksData : ByteString
  }.

Parameter ExtensionRaw : Set.
Parameter Session : Set.
Parameter CipherID : Set.
Parameter Version : Set.

(*
Record ClientHelloMsg :=
  {
    chSession : Session;
    chExtension : list ExtensionRaw;
    chCiphers : list CipherID
  }.
*)
Parameter serverGroups : list Group.

Fixpoint findKeyShare ks gs :=
  match gs with
  | [] => None
  | g::gs' =>
    match find (fun k => Group_beq (ksGroup k) g) ks with
    | Some k => Some k
    | None => findKeyShare ks gs'
    end
  end.

Definition intersect (xs ys : list Group) :=
  filter (fun x => if in_dec Group_eq_dec x ys then true else false) xs.

Parameter Word8 : Set.

Inductive HashAlgorithm :=
  HashNone          
| HashMD5
| HashSHA1
| HashSHA224
| HashSHA256
| HashSHA384
| HashSHA512
| HashIntrinsic
| HashOther : Word8 -> HashAlgorithm.

Inductive SignatureAlgorithm :=
  SignatureAnonymous
| SignatureRSA
| SignatureDSS
| SignatureECDSA
| SignatureRSApssRSAeSHA256
| SignatureRSApssRSAeSHA384
| SignatureRSApssRSAeSHA512
| SignatureEd25519
| SignatureEd448
| SignatureRSApsspssSHA256
| SignatureRSApsspssSHA384
| SignatureRSApsspssSHA512
| SignatureOther : Word8 -> SignatureAlgorithm.

Parameter Word8_beq : Word8 -> Word8 -> bool.

Definition HashAndSignatureAlgorithm := HashAlgorithm * SignatureAlgorithm.

Definition isHashSignatureValid '(h,sig) :=
  match h with
  | HashIntrinsic =>
    match sig with
    | SignatureRSApssRSAeSHA256
    | SignatureRSApssRSAeSHA384
    | SignatureRSApssRSAeSHA512
    | SignatureEd25519
    | SignatureEd448
    | SignatureRSApsspssSHA256
    | SignatureRSApsspssSHA384
    | SignatureRSApsspssSHA512 =>
      true
    | _ => false
    end
  | HashSHA256
  | HashSHA384
  | HashSHA512 =>
    match sig with
    | SignatureECDSA => true
    | _ => false
    end
  | _ => false
  end.

Parameter extension_KeyShare : list ExtensionRaw -> option (list KeyShare).
Parameter extension_NegotiatedGroups : list ExtensionRaw -> option (list Group).
Parameter Word32 : Set.
Parameter PublicKey PrivateKey : Set.
Parameter GroupPublic GroupKey : Set.
Parameter Hash Cipher : Set.
Parameter KeyUpdate : Set.
Parameter Certificate CertificateChain : Set.
Parameter Signature : Set.

Inductive RecvType := RFinished | RClientHello | RAppData | RCCS.

Scheme Equality for RecvType.

Inductive CServerRandom := SR : ByteString -> CServerRandom.
Inductive CClientRandom := CRn : ByteString -> CClientRandom.

Inductive CHandshake :=
| HClientHello : Version -> CClientRandom -> Session -> list CipherID -> list ExtensionRaw -> CHandshake
| HServerHello : CServerRandom -> Session -> CipherID -> list ExtensionRaw -> CHandshake
| HNewSessionTicket : Word32 -> Word32 -> ByteString -> ByteString -> list ExtensionRaw -> CHandshake
| HEndOfEarlyData : CHandshake
| HEncryptedExtensions : list ExtensionRaw -> CHandshake
| HCertRequest : ByteString -> list ExtensionRaw -> CHandshake
| HCertificate : ByteString -> CertificateChain -> list (list ExtensionRaw) -> CHandshake
| HCertVerify : HashAndSignatureAlgorithm -> Signature -> CHandshake
| HFinished : ByteString -> CHandshake
| HKeyUpdate : KeyUpdate -> CHandshake.
(*
Definition  CPacket :=
  list CHandshake + unit + ByteString.
 *)

Inductive AlertLevel := Alert_Warning | Alert_Fatal.

Inductive AlertDescription :=
| CloseNotify
| UnexpectedMessage
| BadRecordMac
| DecryptionFailed
| RecordOverflow
| DecompressionFailure
| HandshakeFailure
| BadCertificate
| UnsupportedCertificate
| CertificateRevoked
| CertificateExpired
| CertificateUnknown
| IllegalParameter
| UnknownCa
| AccessDenied
| DecodeError
| DecryptError
| ExportRestriction
| ProtocolVersion
| InsufficientSecurity
| InternalError
| InappropriateFallback
| UserCanceled
| NoRenegotiation
| MissingExtension
| UnsupportedExtension
| CertificateUnobtainable
| UnrecognizedName
| BadCertificateStatusResponse
| BadCertificateHashValue
| UnknownPskIdentity
| CertificateRequired
| NoApplicationProtocol.

Inductive CPacket :=
| PHandshake : list CHandshake -> CPacket
| PAlert : list (AlertLevel * AlertDescription) -> CPacket
| PChangeCipherSpec : CPacket
| PAppData : ByteString -> CPacket.

Record ClientHelloMsg :=
  { chVersion : Version;
    chRand : ByteString;
    chSess : Session;
    chCipherIDs : list CipherID;
    chExt : list ExtensionRaw
  }.
                 
Definition clientHello (h : CHandshake) :=
  match h with
  | HClientHello v (CRn rand) sess cipherIDs ext =>
    Some {| chVersion:=v; chRand:=rand; chSess:=sess; chCipherIDs:=cipherIDs; chExt:=ext |}
  | _ => None
  end.

Definition finished (h : CHandshake) :=
  match h with
  | HFinished bs => Some bs
  | _ => None
  end.

Definition alert (h : CPacket) :=
  match h with
  | PAlert a => Some a
  | _ => None
  end.

Definition handshake (p : CPacket) :=
  match p with
  | PHandshake [h] => Some h
  | _ => None
  end.

Definition changeCipherSpec (p : CPacket) :=
  match p with
  | PChangeCipherSpec => Some tt
  | _ => None
  end.

Definition appData (p : CPacket) :=
  match p with
  | PAppData dat => Some dat
  | _ => None
  end.

Parameter decodePacket : option (Hash * Cipher * ByteString * nat) -> ByteString -> option CPacket.


(*
Inductive eff_tls :=
| recvClientHello : eff_tls
| recvFinished : option (Hash * Cipher * ByteString) -> eff_tls
| recvCCS : eff_tls
| recvAppData : option (Hash * Cipher * ByteString) -> eff_tls
| getRandomBytes : nat -> eff_tls
| sendPacket : Packet13 * option (Hash * Cipher * ByteString * nat) -> eff_tls
| groupGetPubShared : GroupPublic -> eff_tls
| makeCertVerify : PublicKey * PrivateKey * HashAndSignatureAlgorithm * ByteString -> eff_tls.
*)

Definition option_beq {A} (A_beq : A -> A -> bool) o1 o2 :=
  match o1, o2 with
  | None, None => true
  | Some a1, Some a2 => A_beq a1 a2
  | _,_ => false
  end.

Parameter HostName : Set.
Parameter CipherID_beq : CipherID -> CipherID -> bool.
Parameter cipherID : Cipher -> CipherID.
Parameter Hash_beq : Hash -> Hash -> bool.
Parameter cipherHash : Cipher -> Hash.

Parameter Version_beq : Version -> Version -> bool.
Parameter ByteString_beq : ByteString -> ByteString -> bool.

Open Scope bool_scope.

Parameter Blength : ByteString -> nat.

Parameter extensionEncode_KeyShare : KeyShare -> ByteString.
Parameter extensionEncode_SupportedVersions : Version -> ByteString.
Parameter TLS13 : Version.
Parameter extensionRaw_KeyShare : ByteString -> ExtensionRaw.
Parameter extensionRaw_SupportedVersions : ByteString -> ExtensionRaw.
Parameter extensionLookup_SignatureAlgorithms : list ExtensionRaw -> option ByteString.
Parameter extensionDecode_SignatureAlgorithms : ByteString -> option (list HashAndSignatureAlgorithm).
Parameter extension_SignatureAlgorithms : list ExtensionRaw -> option (list (HashAndSignatureAlgorithm)).


Parameter getCertificates : CertificateChain -> list Certificate.
Parameter defaultCertChain : PublicKey -> CertificateChain.
Parameter empty : ByteString.
Parameter ciphersuite_default : list Cipher.
Parameter hashWith : Hash -> list ByteString -> ByteString.
Parameter sniExt : ExtensionRaw.

Parameter encodeEncryptedExt : list ExtensionRaw -> ByteString.
Parameter CryptoError : Set.
Parameter encodeGroupPublic : GroupPublic -> ByteString.
Parameter decodeGroupPublic : Group -> ByteString -> option GroupPublic.
Parameter ba_convert : GroupKey -> ByteString.
Parameter hashDigestSize : Hash -> nat.

Parameter b_replicate : nat -> Word8 -> ByteString.
Parameter w0 : Word8.
Parameter hkdfExtract : Hash -> ByteString -> ByteString -> ByteString.
Parameter hkdfExpandLabel : Hash -> ByteString -> ByteString -> ByteString -> nat -> ByteString.
Parameter s2b : String.string -> ByteString.
Parameter hmac : Hash -> ByteString -> ByteString -> ByteString.

Fixpoint inb {A} (eqbA: A -> A -> bool) x l :=
  match l with
  | [] => false
  | y::l' => if eqbA x y then
               true
             else
               inb eqbA x l'
  end.

Definition chooseCipher
           (clientCipherIDs : list CipherID)
           (serverCiphers : list Cipher) :=
  hd_error (filter (fun cipher =>
                      inb CipherID_beq (cipherID cipher) clientCipherIDs)
                   serverCiphers).

Definition makeVerifyData (h : Hash)(key : ByteString)(transcript : ByteString) :=
  hmac h (hkdfExpandLabel h key (s2b "finished") (s2b "") (hashDigestSize h)) transcript.

Parameter isDigitalSignaturePair : PublicKey * PrivateKey -> bool.
Parameter signatureCompatible13 : PublicKey -> HashAndSignatureAlgorithm -> bool.
Parameter certPubKey : Certificate -> PublicKey.


Definition credentialDigitaiSignatureKey
           (pub : PublicKey)
           (priv : PrivateKey) :=
  if isDigitalSignaturePair (pub,priv) then
    Some pub
  else
    None.

Fixpoint decideCredInfo'
         (priv : PrivateKey)
         (hashSig : HashAndSignatureAlgorithm)
         (certs : list Certificate) :=
  match certs with
  | [] => None
  | cert::rest =>
    let pub := certPubKey cert in
    if isDigitalSignaturePair (pub, priv) then
      if signatureCompatible13 pub hashSig then
        Some (pub, hashSig)
      else
        decideCredInfo' priv hashSig rest
    else
      decideCredInfo' priv hashSig rest
  end.

Definition decideCredInfo
         (priv : PrivateKey)
         (certs : list Certificate)
         (hashSigs : list (HashAndSignatureAlgorithm)) :=
  (fix aux hss :=
     match hss with
     | [] => None
     | hs::rest =>
       match decideCredInfo' priv hs certs with
       | None => aux rest
       | Some res => Some res
       end
     end) (filter isHashSignatureValid hashSigs).

Definition LF : String.string := String.String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".
Definition CR : String.string := String.String (Coq.Strings.Ascii.Ascii true false true true false false false false) "".

Require Import String.

Parameter mconcat : list ByteString -> ByteString.
Parameter serverCiphers : list Cipher.

Fixpoint replicate {A:Set} n (a:A) :=
  match n with
  | O => []
  | S n' => a::replicate n' a
  end.

Parameter Word64 : Set.

Inductive SessionFlag := SessionEMS : SessionFlag.

Record TicketInfo :=
  { lifetime : Word32;
    ageAdd : Word32;
    txrxTime : Word64;
    estimatedRTT : option Word64
  }.

Parameter CompressionID : Set.
Parameter dummyCompressionID : CompressionID.

Record SessionData :=
  { sessionVersion : Version;
    sessionCipher : CipherID;
    sessionCompression : CompressionID;
    sessionClientSNI : option String.string;
    sessionSecret : ByteString;
    sessionGroup : option Group;
    sessionTicketInfo : option TicketInfo;
    sessionALPN : option ByteString;
    sessionMaxEarlyDataSize : nat;
    sessionFlags : list SessionFlag
  }.

(*
Definition args_tls :=
  String.string * SessionData (* SetPSK *)
  + String.string (* SessionResume *)
  + unit (* GetCurrentTime *)
  + unit (* Close *)
  + CPacket * option (Hash * Cipher * ByteString * nat) (* SendPacket *)
  + nat (* GetRandomBytes *)
  + unit (* RecvData *)
  + GroupPublic (* GroupGetPubShared *)
  + PublicKey * PrivateKey * HashAndSignatureAlgorithm * ByteString (* MakeCertVerify *)
  + Hash * Cipher * ByteString * bool (* SetSecret *)
  + CPacket (* Send *)
  + (unit + unit + unit + unit). (* Recv *)
 *)

Inductive args_tls :=
| setPSK : String.string * SessionData -> args_tls
| sessionResume : String.string -> args_tls
| getCurrentTime : unit -> args_tls
| closeWith : AlertLevel * AlertDescription -> args_tls
| sendData : CPacket * option (Hash * Cipher * ByteString * nat) -> args_tls
| getRandomBytes : nat -> args_tls
| recvData : unit -> args_tls
| groupGetPubShared : GroupPublic -> args_tls
| makeCertVerify : PublicKey * PrivateKey * HashAndSignatureAlgorithm * ByteString -> args_tls
| setSecret : Hash * Cipher * ByteString * bool -> args_tls
| sendPacket : CPacket -> args_tls
| recvPacket : RecvType -> args_tls.

Inductive rets_tls :=
| RetAlert : AlertLevel * AlertDescription -> rets_tls
| FromSetPSK : rets_tls
| FromGetCurrentTime : Word64 -> rets_tls
| FromSessionResume : option SessionData -> rets_tls
| FromSetSecret : rets_tls
| FromSendPacket : ByteString -> rets_tls
| FromGetRandomBytes : ByteString -> rets_tls
| FromMakeCertVerify : CHandshake -> rets_tls
| FromGroupGetPubShared : option (GroupPublic * GroupKey) -> rets_tls
| FromRecvClientHello : ByteString * ClientHelloMsg -> rets_tls
| FromRecvFinished : ByteString -> rets_tls
| FromRecvCCS : rets_tls
| FromRecvAppData : ByteString -> rets_tls
| FromRecvData : ByteString -> rets_tls.

Definition retAlert p :=
  match p with
  | RetAlert a => Some a
  | _ => None
  end.

Definition fromSetSecret p :=
  match p with
  | FromSetSecret => Some tt
  | _ => None
  end.

Definition fromSetPSK p :=
  match p with
  | FromSetPSK => Some tt
  | _ => None
  end.

Definition fromSessionResume p :=
  match p with
  | FromSessionResume a => Some a
  | _ => None
  end.

Definition fromGetCurrentTime p :=
  match p with
  | FromGetCurrentTime a => Some a
  | _ => None
  end.

Definition fromSendPacket p :=
  match p with
  | FromSendPacket a => Some a
  | _ => None
  end.

Definition fromGetRandomBytes p :=
  match p with
  | FromGetRandomBytes a => Some a
  | _ => None
  end.

Definition fromMakeCertVerify p :=
  match p with
  | FromMakeCertVerify a => Some a
  | _ => None
  end.

Definition fromGroupGetPubShared p :=
  match p with
  | FromGroupGetPubShared a => Some a
  | _ => None
  end.

Definition fromRecvClientHello p :=
  match p with
  | FromRecvClientHello a => Some a
  | _ => None
  end.

Definition fromRecvFinished p :=
  match p with
  | FromRecvFinished a => Some a
  | _ => None
  end.

Definition fromRecvCCS p :=
  match p with
  | FromRecvCCS => Some tt
  | _ => None
  end.

Definition fromRecvAppData p :=
  match p with
  | FromRecvAppData a => Some a
  | _ => None
  end.

Definition fromRecvData p :=
  match p with
  | FromRecvData a => Some a
  | _ => None
  end.

(*
Definition rets_tls :=
  option SessionData
  + option (GroupPublic * GroupKey)
  + CHandshake
  + ByteString
  + unit
  + (AlertLevel * AlertDescription + ByteString * ClientHelloMsg).
 *)

Notation "r <- 'yield' 'SetPSK' $ a ; p" :=
  (Eff yield (setPSK a)
       (fun r => p))
    (at level 100, right associativity).

Notation "r <- 'yield' 'SessionResume' $ a ; p" :=
  (Eff yield (sessionResume a)
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromSessionResume r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'GetCurrentTime' $ a ; p" :=
  (Eff yield (getCurrentTime a)
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromGetCurrentTime r')))
       (at level 100, right associativity).

Notation "r <- 'yield' 'Close' $ a ; p" :=
  (Eff yield (closeWith a)
       (fun r => p))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvClientHello' ; p" :=
  (Eff yield (recvPacket RClientHello)
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (closeWith al)
                                                  (fun _ => Return None))
                                   (Return None) (retAlert r'))
                    (fromRecvClientHello r')))
       (at level 100, right associativity).

Notation "r <- 'yield' 'RecvData' $ a ; p" :=
  (Eff yield (recvData a)
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (closeWith al)
                                                  (fun _ => Return inhabitant))
                                   (Return inhabitant) (retAlert r'))
                    (fromRecvData r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvFinished' ; p" :=
  (Eff yield (recvPacket RFinished)
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (closeWith al)
                                                  (fun _ => Return None))
                                   (Return None) (retAlert r'))
                    (fromRecvFinished r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvCCS' ; p" :=
  (Eff yield (recvPacket RCCS)
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (closeWith al)
                                                  (fun _ => Return inhabitant))
                                   (Return inhabitant) (retAlert r'))
                    (fromRecvCCS r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvAppData' ; p" :=
  (Eff yield (recvPacket RAppData)
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (closeWith al)
                                                  (fun _ => Return None))
                                   (Return None) (retAlert r'))
                    (fromRecvAppData r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'GetRandomBytes' $ a ; p" :=
  (Eff yield (getRandomBytes a)
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromGetRandomBytes r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'SendPacket' $ a ; p" :=
  (Eff yield (sendPacket a)
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromSendPacket r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'GroupGetPubShared' $ a ; p" :=
  (Eff yield (groupGetPubShared a)
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromGroupGetPubShared r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'MakeCertVerify' $ a ; p" :=
  (Eff yield (makeCertVerify a)
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromMakeCertVerify r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'SetSecret' $ a ; p" :=
  (Eff yield (setSecret a)
       (fun r => p))
    (at level 100, right associativity).


Instance sigT_rets_inhabit : Inhabit rets_tls :=
  { inhabitant := FromSetPSK }.

Instance sigT_args_inhabit : Inhabit args_tls :=
  { inhabitant := getCurrentTime tt }.

Parameter ProtocolType : Set.
Parameter Header : Set.
Parameter hdReadLen : Header -> nat.
(*
Inductive Header := header : ProtocolType -> Version -> nat -> Header.

Definition hdReadLen hd :=
  match hd with
  | header _ _ n => n
  end.
 *)

Parameter Bsplit :  nat -> ByteString -> ByteString * ByteString.

Notation "x <~ 'ifSome' o {{ q }} p" :=
  (option_branch (fun x => p) q o)
    (at level 100, right associativity).

Inductive PskKexMode := PSK_KE | PSK_DHE_KE.
Scheme Equality for PskKexMode.

Inductive ServerNameType :=
| ServerNameHostName : String.string -> ServerNameType
| ServerNameOther : Word8 * ByteString -> ServerNameType.

Inductive ServerName := Build_ServerName : list ServerNameType -> ServerName.

Fixpoint find {A:Set} (f : A -> bool) (l : list A) :=
  match l with
  | [] => None
  | a::l' => if f a then Some a else find f l'
  end.

Definition checkSessionEquality usedCipher ciphers malpn sdata :=
  let isSameCipher := CipherID_beq (sessionCipher sdata) (cipherID usedCipher) in
  let isSameKDF :=
      match find (fun c => CipherID_beq (cipherID c) (sessionCipher sdata)) ciphers with
      | None => false
      | Some c => Hash_beq (cipherHash c) (cipherHash usedCipher)
      end
  in
  let isSameALPN := option_beq ByteString_beq (sessionALPN sdata) malpn in
  (isSameKDF, isSameCipher && isSameALPN).

Inductive PskIdentity := Build_PskIdentity : ByteString -> Word32 -> PskIdentity.

Inductive PreSharedKey :=
| PreSharedKeyClientHello : list PskIdentity -> list ByteString -> PreSharedKey
| PreSharedKeyServerHello : nat -> PreSharedKey.

Parameter extension_PreSharedKey : list ExtensionRaw -> option PreSharedKey.
Parameter extension_ALPN : list ExtensionRaw -> option ByteString.

Definition extension_PreSharedKeyCH exts :=
  match extension_PreSharedKey exts with
  | Some (PreSharedKeyClientHello (Build_PskIdentity sessionID obfAge :: _) bnds) =>
    Some (sessionID, obfAge, bnds)
  | _ => None
  end.

Definition sumnat l :=
  fold_left Nat.add l 0.
Parameter b2s : ByteString -> String.string.
Parameter Word32minus : Word32 -> Word32 -> Word32.
Parameter Word64plus Word64minus Word64max : Word64 -> Word64 -> Word64.
Parameter Word64gt : Word64 -> Word64 -> bool.
Parameter Word32le : Word32 -> Word32 -> bool.
Parameter w64_2000 : Word64.
Parameter w32to64 : Word32 -> Word64.

Instance bool_inhabitant : Inhabit bool :=
  { inhabitant := true }.

Definition checkFreshness tinfo obfAge serverReceiveTime :=
  match estimatedRTT tinfo with
  | None => false
  | Some rtt =>
    let age := Word32minus obfAge (ageAdd tinfo) in
    let expectedArrivalTime := Word64plus (txrxTime tinfo) (Word64plus rtt (w32to64 age)) in
    let freshness := if Word64gt expectedArrivalTime serverReceiveTime then
                       Word64minus expectedArrivalTime serverReceiveTime
                     else Word64minus serverReceiveTime expectedArrivalTime
    in
    Word32le age (lifetime tinfo) && Word64gt (Word64max rtt w64_2000) freshness
  end.

Instance ByteString_inhabitant : Inhabit ByteString :=
  { inhabitant := empty }.


Definition choosePSK exts dhModes usedCipher ciphers zero
  : t (const_yield args_tls) (const_yield rets_tls) (ByteString * option (_ * nat * nat) * bool) :=
  match extension_PreSharedKeyCH exts with
  | None =>
    Return (zero, None, false)
  | Some (sessionID, obfAge, bnds) =>
    bnd <~ ifSome hd_error bnds {{ Return (zero, None, false) }}
    if inb PskKexMode_beq PSK_DHE_KE dhModes then
      let len := (sumnat (map (fun x => Blength x + 1) bnds) + 2)%nat in
      osdata <- yield SessionResume $ (b2s sessionID);
      sdata <~ ifSome osdata {{ Return (zero, None, false) }}
      tinfo <~ ifSome sessionTicketInfo sdata {{ Return (zero, None, false) }}
      let psk := sessionSecret sdata in
      serverReceiveTime <- yield GetCurrentTime $ tt;
      let isFresh := checkFreshness tinfo obfAge serverReceiveTime in
      let malpn := extension_ALPN exts in
      let (isPSKValid, is0RTTValid) := checkSessionEquality usedCipher ciphers malpn sdata in
      if isPSKValid && isFresh then
        Return (psk, Some (bnd, 0, len), is0RTTValid)
      else Return (zero, None, false)
    else Return (zero, None, false)
  end.

Parameter Btake : nat -> ByteString -> ByteString.


Definition makePSKBinder chEncoded sec usedHash truncLen hsize :=
  let msg := Btake (Blength chEncoded - truncLen) chEncoded in
  let hChTruncated := hashWith usedHash [msg] in
  let binderKey := hkdfExpandLabel usedHash sec (s2b "res binder") (hashWith usedHash [s2b""]) hsize in
  makeVerifyData usedHash binderKey hChTruncated.

Parameter extensionEncode_PreSharedKey : PreSharedKey -> ByteString.
Parameter ExtensionRaw_PreSharedKey : ByteString -> ExtensionRaw.

Definition checkBinder chEncoded usedHash earlySecret binderInfo hsize :=
  match binderInfo with
  | None => Some []
  | Some (binder, n, tlen) =>
    let binder' := makePSKBinder chEncoded earlySecret usedHash tlen hsize in
    if ByteString_beq binder' binder then
      let selectedIdentity := extensionEncode_PreSharedKey (PreSharedKeyServerHello n) in
      Some [ExtensionRaw_PreSharedKey selectedIdentity]
    else None
  end.
 
Fixpoint chooseServerName' ns :=
  match ns with
  | [] => None
  | name::rest =>
    match name with
    | ServerNameHostName hostName => Some hostName
    | _ => chooseServerName' rest
    end
  end.

Parameter extension_ServerName : list ExtensionRaw -> option ServerName.

Definition chooseServerName exts :=
  match extension_ServerName exts with
  | None => None
  | Some (Build_ServerName ns) => chooseServerName' ns
  end.

Parameter encodeHandshake13 : CHandshake -> ByteString.
Parameter extension_PskKeyModes : list ExtensionRaw -> option (list PskKexMode).
Parameter nat2Word32 : nat -> Word32.
Parameter messageHash00 : ByteString.
Parameter natToBytes : nat -> ByteString.
Parameter hrrRandom : CServerRandom.

Definition isSome {A:Set} (o : option A) :=
  match o with
  | Some _ => true
  | None => false
  end.

Parameter extensionEncode_KeyShareHRR : Group -> ByteString.
Parameter extensionEncode_SupportedVersionsServerHello : Version -> ByteString.

Definition doHelloRetryRequest chEncoded' ch hash cipher
  : t (const_yield args_tls) (const_yield rets_tls) (option (list ByteString * ClientHelloMsg * KeyShare)) :=
  Def (fun al => (_ <- yield Close $ (Alert_Fatal, al);
                 Return None) : t (const_yield args_tls) (const_yield rets_tls) (option (list ByteString * ClientHelloMsg * KeyShare))) (fun alert =>
  Let chHashed := hashWith hash [chEncoded'] in

  let clientGroups :=
      match extension_NegotiatedGroups ch.(chExt) with
      | Some gs => gs
      | None => []
      end
  in
  let possibleGroups := intersect serverGroups clientGroups in
  match hd_error possibleGroups with
  | None => alert HandshakeFailure
  | Some g =>
    let serverKeyShare := extensionEncode_KeyShareHRR g in
    let selectedVersion := extensionEncode_SupportedVersionsServerHello TLS13 in
    let extensions := [extensionRaw_KeyShare serverKeyShare;
                         extensionRaw_SupportedVersions selectedVersion]
    in
    let hrr := HServerHello hrrRandom ch.(chSess) (cipherID cipher) extensions in
    hrrEncoded <- yield SendPacket $ PHandshake [hrr];
    _ <- yield SendPacket $ PChangeCipherSpec;
    d <- yield RecvClientHello;
    let (chEncoded, chnew) := (d : ByteString * ClientHelloMsg) in
    Let transcript := [messageHash00; natToBytes (Blength chHashed); chHashed; hrrEncoded; chEncoded] in
    keyShares <~ ifSome extension_KeyShare chnew.(chExt)
      {{ alert IllegalParameter }}
    match hd_error keyShares with
    | None => alert IllegalParameter
    | Some keyShare =>
      if negb (Group_beq g keyShare.(ksGroup)) then
        alert IllegalParameter
      else
      Return (Some (transcript, chnew, keyShare))
    end
  end).

Parameter extension_SupportedVersionsCH : list ExtensionRaw -> option (list Version).
Parameter bytes2w32 : ByteString -> Word32.
Parameter life : Word32.

Fixpoint clientKeySharesValid ks gs :=
  match ks,gs with
  | k::ks',g::gs' =>
    if Group_beq (ksGroup k) g then
      clientKeySharesValid ks' gs'
    else
      clientKeySharesValid (k::ks') gs'
  | [],_ => true
  | _,[] => false
  end.

Parameter extension_SupportedGroups : list ExtensionRaw -> option (list Group).
Parameter pskkey : option ByteString.

Definition fl := 1000.
Definition doHandshake (fuel:nat) (cch: CertificateChain)(pr: PrivateKey)(_: rets_tls)
  : t (const_yield args_tls) (const_yield rets_tls) (option unit) :=
  Def (fun al => _ <- yield Close $ (Alert_Fatal, al);
                 Return None) (fun alert =>
  let certs := getCertificates cch in
  d' <- yield RecvClientHello;
  let (chEncoded, se) := (d' : ByteString * ClientHelloMsg) in
  let sess := chSess se in
  let chExts := chExt se in
  let cipherIDs := chCipherIDs se in
  let oVer :=
      match extension_SupportedVersionsCH chExts with
      | None => None
      | Some vers =>
        if inb Version_beq TLS13 vers then
          Some TLS13
        else None
      end
  in
  chosenVer <~ ifSome oVer
    {{ alert ProtocolVersion }}
  cipher <~ ifSome chooseCipher cipherIDs serverCiphers
    {{ alert HandshakeFailure }}
  let usedHash := cipherHash cipher in
  let keyShares :=
      match extension_KeyShare chExts with
      | None => []
      | Some kss => kss
      end
  in
  let cSupportedGroups :=
      match extension_SupportedGroups chExts with
      | None => []
      | Some gs => gs
      end
  in
  if negb (clientKeySharesValid keyShares cSupportedGroups) then
    alert IllegalParameter
  else
  let oks := findKeyShare keyShares serverGroups in
  o <<- match oks with
        | None => doHelloRetryRequest chEncoded se usedHash cipher
        | Some keyShare =>
          Return (Some ([chEncoded], se, keyShare))
        end;
  d <~ ifSome o
    {{ alert IllegalParameter }}
  let (tch, keyShare) := (d : list ByteString * ClientHelloMsg * KeyShare) in
  let (transcript', ch) := (tch : list ByteString * ClientHelloMsg) in
  let sess := chSess ch in
  let chExts := chExt ch in
  cpub <~ ifSome decodeGroupPublic (ksGroup keyShare) (ksData keyShare)
    {{ alert IllegalParameter }}
  mecdhePair <- yield GroupGetPubShared $ cpub;
  ecdhePair <~ ifSome mecdhePair
    {{ alert IllegalParameter }}
  Let wspub := encodeGroupPublic (fst ecdhePair) in
  Let ecdhe := ba_convert (snd ecdhePair) in
  let serverKeyShare := {| ksGroup := ksGroup keyShare; ksData := wspub |} in
  let osni := chooseServerName chExts in
  let eExts := match osni with
               | None => []
               | Some _ => [sniExt]
               end
  in
  
  (* sendServerHello *)
  Let ks := extensionEncode_KeyShare serverKeyShare in
  let selectedVersion := extensionEncode_SupportedVersions TLS13 in

  let hsize := hashDigestSize usedHash in
  let zero := b_replicate hsize w0 in
  let dhModes := match extension_PskKeyModes chExts with
                 | Some ms => ms
                 | None => []
                 end
  in
  p <<- choosePSK chExts dhModes cipher serverCiphers zero;
  let (pb, is0RTTValid) := p : ByteString * option (ByteString * nat * nat) * bool in
  let (psk, binderInfo) := pb in
  let earlySecret := hkdfExtract usedHash zero psk in
  extensions <~ ifSome checkBinder chEncoded usedHash earlySecret binderInfo hsize
    {{ alert DecryptError }}
  let extensions' :=
      extensionRaw_KeyShare ks :: extensionRaw_SupportedVersions selectedVersion  :: extensions
  in
  ohashSigs <<-
            if is0RTTValid then
              Return None
            else
              bs <~ ifSome extensionLookup_SignatureAlgorithms chExts
                  {{ _ <- yield Close $ (Alert_Fatal, MissingExtension);
                     Return None }}
              hashSigs <~ ifSome extensionDecode_SignatureAlgorithms bs
                {{ _ <- yield Close $ (Alert_Fatal, DecodeError); Return None }}
              pubhs <~ ifSome decideCredInfo pr certs hashSigs
                {{ _ <- yield Close $ (Alert_Fatal, HandshakeFailure); Return None }}
              Return (Some pubhs);
  (*
  ohashSigs <<- _ <~ ifSome binderInfo
            {{ bs <~ ifSome extensionLookup_SignatureAlgorithms chExts
                  {{ _ <- yield Close $ (Alert_Fatal, MissingExtension);
                     Return None }}
               hashSigs <~ ifSome extensionDecode_SignatureAlgorithms bs
                 {{ _ <- yield Close $ (Alert_Fatal, DecodeError); Return None }}
               pubhs <~ ifSome decideCredInfo pr certs hashSigs
                 {{ _ <- yield Close $ (Alert_Fatal, HandshakeFailure); Return None }}
               Return (Some pubhs)  }}
            Return None;
*)
  srand <- yield GetRandomBytes $ 32;
  shEncoded <- yield SendPacket $
            (PHandshake [HServerHello (SR srand) sess (cipherID cipher) extensions']);

  (* calculate handshake secrets *)
  Let hCh := hashWith usedHash (transcript' ++ [shEncoded])%list in
  let clientEarlySecret := hkdfExpandLabel usedHash earlySecret (s2b "c e traffic") hCh hsize in
  
  let handshakeSecret := hkdfExtract usedHash (hkdfExpandLabel usedHash earlySecret (s2b "derived") (hashWith usedHash [s2b ""]) hsize) ecdhe in
  let clientHandshakeSecret := hkdfExpandLabel usedHash handshakeSecret (s2b "c hs traffic") hCh hsize in
  let serverHandshakeSecret := hkdfExpandLabel usedHash handshakeSecret (s2b "s hs traffic") hCh hsize in

  _ <<-
    if Nat.ltb 2 (List.length transcript') then
      Return tt
    else
      _ <- yield SendPacket $ PChangeCipherSpec; Return tt;
  _ <- yield SetSecret $ (usedHash, cipher, serverHandshakeSecret, false);
  extEncoded <- yield SendPacket $
             (PHandshake [HEncryptedExtensions eExts]);
  let sendCertAndVerify :=
      Let transcript := (transcript' ++ [shEncoded; extEncoded])%list in
      match ohashSigs with
      | None => Return (Some transcript)
      | Some pubhs =>
        let (pub,hashSig) := pubhs : PublicKey * HashAndSignatureAlgorithm in
        certEncoded <- yield SendPacket $
                    (PHandshake [HCertificate empty cch [[]]]);
        let hashed := hashWith (cipherHash cipher) (transcript ++ [certEncoded]) in
        cv <- yield MakeCertVerify $ (pub,pr,hashSig,hashed);
        cvEncoded <- yield SendPacket $ (PHandshake [cv]);
        Return (Some (transcript ++ [certEncoded; cvEncoded])%list)
      end
  in
  otranscript <<- sendCertAndVerify;
  transcript <~ ifSome otranscript {{ Return None }}
  
  let hashed' := hashWith usedHash transcript in
  finEncoded <- yield SendPacket $
             (PHandshake [HFinished (makeVerifyData usedHash serverHandshakeSecret hashed')]);
  Let tran := (transcript ++ [finEncoded])%list in
  sfSentTime <- yield GetCurrentTime $ tt;
  let hashed'' := hashWith usedHash tran in
  let applicationSecret := hkdfExtract usedHash (hkdfExpandLabel usedHash handshakeSecret (s2b "derived") (hashWith usedHash [s2b ""]) hsize) zero in
  let clientApplicationSecret := hkdfExpandLabel usedHash applicationSecret (s2b "c ap traffic") hashed'' hsize in
  let serverApplicationSecret := hkdfExpandLabel usedHash applicationSecret (s2b "s ap traffic") hashed'' hsize in
  _ <- yield SetSecret $ (usedHash, cipher, serverApplicationSecret, false);

  _ <- yield SetSecret $ (usedHash, cipher, clientHandshakeSecret, true);
  fin <- yield RecvFinished;
  cfRecvTime <- yield GetCurrentTime $ tt;

  (* calculate application secrets *)
  let hashed''' := hashWith usedHash (tran ++ [encodeHandshake13 (HFinished fin)]) in
  let resumptionMasterSecret := hkdfExpandLabel usedHash applicationSecret (s2b "res master") hashed''' hsize in
  _ <- yield SetSecret $ (usedHash, cipher, clientApplicationSecret, true);
  if ByteString_beq fin (makeVerifyData usedHash clientHandshakeSecret hashed'') then
    b <- yield GetRandomBytes $ 36;
      let nonceBAgeAdd := Bsplit 4 b in
      let nonce := snd nonceBAgeAdd in
      let bAgeAdd := fst nonceBAgeAdd in
    let bAdd := bytes2w32 bAgeAdd in
    Let tinfo := {| lifetime := life;
                    ageAdd := bAdd;
                    txrxTime := cfRecvTime;
                    estimatedRTT := Some (Word64minus cfRecvTime sfSentTime) |}
    in
    Let pac := PHandshake [HNewSessionTicket life bAdd nonce (s2b "test") []] in
    _ <- yield SetPSK $ ("test",
                         {| sessionVersion := TLS13;
                            sessionCipher := cipherID cipher;
                            sessionGroup := None;
                            sessionTicketInfo := Some tinfo;
                            sessionCompression := dummyCompressionID;
                            sessionClientSNI := osni;
                            sessionSecret := match pskkey with
                                             | Some key => key
                                             | None => hkdfExpandLabel usedHash resumptionMasterSecret (s2b "resumption") nonce hsize
                                             end;
                            sessionALPN := None;
                            sessionMaxEarlyDataSize := 5;
                            sessionFlags := []
                         |});
                 _ <- yield SendPacket $ pac;
                 (*
    data <- yield RecvAppData;
    x <- yield SendPacket $ (PAppData (mconcat ([s2b ("HTTP/1.1 200 OK" ++ CR ++ LF ++ "Content-Type: text/plain" ++ CR ++ LF ++ CR ++ LF ++ "Hello, "); data; s2b ("!" ++ CR ++ LF)])));
    _ <- yield Close $ (Alert_Warning, CloseNotify); Return None
*)
      (*
    _ <- yield SendPacket $ pac;
    _ <- yield Close $ tt;
    Return tt
*)
    nat_rect_nondep
      (fun _ => _ <- yield Close $ (Alert_Warning, CloseNotify); Return None)
      (fun _ rec _ =>
         data <- yield RecvAppData;
         x <- yield SendPacket $ (PAppData (mconcat ([s2b ("HTTP/1.1 200 OK" ++ CR ++ LF ++ "Content-Type: text/plain" ++ CR ++ LF ++ "Content-Length: 6" ++ CR ++ LF ++ CR ++ LF ++ "Hello!" ++ CR ++ LF)])));
         rec tt)
      fl tt

  else
    alert DecryptError)
.

Definition doHandshake_derive :
  { state & { step &
              forall fuel certs priv,
                { init | @equiv_coro _ _ _ _ _ state step init (doHandshake fuel certs priv) } } }.
Proof.
  do 3 eexists.
(*
  unfold doHandshake.
  intros.
  Time unshelve derive_coro (tt,fuel,certs,priv); intros; exact inhabitant.
  Time Defined.
*)
  lazymatch goal with
    |- ?x => assert x
  end.
  unfold doHandshake.
  intros.
  Time unshelve derive_coro (tt,fuel,certs,priv); intros; exact inhabitant.
  
  lazymatch goal with
    |- @equiv_coro _ _ _ _ _ ?state ?step _ _ =>
    idtac state
  end.
  lazymatch goal with
    |- @equiv_coro _ _ _ _ _ ?state ?step _ _ =>
    assert Set;
      [ pose state as st; transparent_abstract (exact st) using doHandshake_state
      |];
    assert (step_type (const_yield args_tls) (const_yield rets_tls) (option unit) doHandshake_state);
    [ pose step as stp; transparent_abstract (exact stp) using doHandshake_step|]
  end.
  Time Admitted.


Axiom doHandshake_equiv : forall fuel certs keys,
  equiv_coro doHandshake_step (inl (tt,fuel,certs,keys)) (doHandshake fuel certs keys).

(*
Definition doHandshake_step := projT1 (projT2 doHandshake_derive).

Definition doHandshake_equiv fuel certs keys :
  equiv_coro doHandshake_step (inl (tt,fuel,certs,keys)) (doHandshake fuel certs keys) :=
  proj2_sig (projT2 (projT2 doHandshake_derive) fuel certs keys).
*)

Hint Resolve doHandshake_equiv : equivc.

Notation "r <- 'yield' 'SendData' $ a ; p" :=
  (Eff yield (sendData a)
       (fun r => p))
    (at level 100, right associativity).
(*
Notation "r <- 'yield' 'SendData' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inl (inl (inr a))))))))
       (fun r => p))
    (at level 100, right associativity).
 *)


Inductive CProtocolType :=
| CProtocolType_ChangeCipherSpec
| CProtocolType_Alert
| CProtocolType_Handshake
| CProtocolType_AppData
| CProtocolType_DeprecatedHandshake.

Parameter TLSError : Set.
Parameter errorToAlert : TLSError -> AlertLevel * AlertDescription.

Inductive ParseResult (a:Set) :=
| PError : TLSError -> ParseResult a
| PPartial : (ByteString -> ParseResult a) -> ParseResult a
| PSuccess : a -> ParseResult a
| PSuccessRemaining : a -> ByteString -> ParseResult a.

Definition isPError {a} (x : ParseResult a) :=
  match x with
  | PError _ err => Some (errorToAlert err)
  | _ => None
  end.

Definition isPPartial {a} (x : ParseResult a) :=
  match x with
  | PPartial _ cont => Some cont
  | _ => None
  end.

Definition isPSuccess {a} (x : ParseResult a) :=
  match x with
  | PSuccess _ p => Some p
  | _ => None
  end.

Scheme Equality for CProtocolType.

Parameter HandshakeType : Set.

Parameter decodeHeader : ByteString -> AlertDescription + Header.
Parameter decodeRecord : Header -> option (Hash * Cipher * ByteString * nat) -> ByteString -> AlertDescription + CProtocolType * ByteString.
Parameter parseHandshakeRecord : option (ByteString -> ParseResult (HandshakeType * ByteString)) -> ByteString -> ParseResult (HandshakeType * ByteString).
Parameter parseHandshake : HandshakeType * ByteString -> AlertLevel * AlertDescription + CHandshake.
Parameter dummyCCS : ByteString.

Definition decode boCont header bs (s:RecvType) o : t (const_yield args_tls) (const_yield rets_tls) (option (_ + rets_tls)) :=
  let (b,oCont) := (boCont : ByteString * option (ByteString -> ParseResult _))in
  match decodeRecord header o bs with
  | inl al => Return (Some (inr (RetAlert (Alert_Fatal, al))))
  | inr (ty,bs') =>
    if CProtocolType_beq ty CProtocolType_Handshake then
      let p := parseHandshakeRecord oCont bs' in
      match isPError p with
      | Some al => Return (Some (inr (RetAlert al)))
      | None =>
        match isPPartial p with
        | Some cont => Return (Some (inl (mconcat [b;bs], cont)))
        | None =>
          match isPSuccess p with
          | Some r =>
            match parseHandshake r with
            | inl al => Return (Some (inr (RetAlert al)))
            | inr h =>
              match finished h with
              | Some fin =>
                if RecvType_beq s  RFinished then
                  Return (Some (inr (FromRecvFinished fin)))
                else
                  Return (Some (inr (RetAlert (Alert_Fatal, UnexpectedMessage))))
              | None =>
                match clientHello h with
                | Some ch =>
                  if RecvType_beq s RClientHello then
                    Return (Some (inr (FromRecvClientHello (mconcat [b;bs],ch))))
                  else
                    Return (Some (inr (RetAlert (Alert_Fatal, UnexpectedMessage))))
                | None =>
                  Return (Some (inr (RetAlert (Alert_Fatal, UnexpectedMessage))))
                end
              end
            end
          | None => Return (Some (inr (RetAlert (Alert_Fatal, DecodeError))))
          end
        end
      end
    else
      match oCont with
      | Some _ => Return (Some (inr (RetAlert (Alert_Fatal, UnexpectedMessage))))
      | None =>
        if CProtocolType_beq ty CProtocolType_AppData then
          if RecvType_beq s RAppData then
            Return (Some (inr (FromRecvAppData bs')))
          else
            Return (Some (inr (RetAlert (Alert_Fatal, UnexpectedMessage))))
        else
          Return (Some (inr (RetAlert (Alert_Fatal, UnexpectedMessage))))
      end
  end.

Parameter maxCiphertextSize maxPlaintextSize : nat.

(*
Notation "r <- 'yield' 'RecvData_' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inr a))))))
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (inl (inr (PAlert [al])))
                                                  (fun _ => Return inhabitant))
                                   (Return inhabitant) (retAlert r'))
                    (fromRecvData r')))
    (at level 100, right associativity).
*)

Definition isRecvPacket p :=
  match p with
  | recvPacket a => Some a
  | _ => None
  end.

Definition isSendPacket p :=
  match p with
  | sendPacket a => Some a
  | _ => None
  end.

Definition isSetSecret p :=
  match p with
  | setSecret a => Some a
  | _ => None
  end.

Definition isCloseWith p :=
  match p with
  | closeWith a => Some a
  | _ => None
  end.

Parameter hdProtocolType : Header -> CProtocolType.

Definition readWrite fuel certs keys(_: rets_tls) : t (const_yield _) (const_yield rets_tls) (option String.string) :=
  pipe (doHandshake fuel certs keys) (fun coro : coro_type doHandshake_step =>
  nat_rect_nondep
    (fun _ => Return None)
    (fun _ rec (ctx: option (Hash * Cipher * ByteString * nat) * option (Hash * Cipher * ByteString * nat) * option (RecvType * (ByteString * option (ByteString -> ParseResult (HandshakeType * ByteString)))) * ByteString * rets_tls * coro_type doHandshake_step) =>

       match ctx with
       | (recvinfo,sendinfo,omtype,bs,a,c) =>
       match omtype with
       | None =>
         r <- resume c $ a;
         match isRecvPacket r with
         | Some mtype =>
           _ <- yield (getRandomBytes 0); (* needed for compiler limitation *)
           rec (recvinfo, sendinfo, Some (mtype, (empty, None)), bs, a, c)
         | None =>
           match isSendPacket r with
           | Some pkt  =>
             match sendinfo with
             | None =>
               a' <- yield SendData $ (pkt, None);
               rec (recvinfo, None, None, bs, a', c)
             | Some (q,num) =>
               a' <- yield SendData $ (pkt, (Some (q, num)));
               rec (recvinfo, Some (q, S num), None, bs, a', c)
             end
           | None =>
             match isCloseWith r with
             | Some al =>
               match sendinfo with
               | None =>
                 _ <- yield SendData $ (PAlert [al], None);
                 a' <- yield Close $ al;
                 rec (recvinfo, None, None, bs, a', c)
               | Some (q,num) =>
                 _ <- yield SendData $ (PAlert [al], Some (q,num));
                 a' <- yield Close $ al;
                 rec (recvinfo, Some (q, S num), None, bs, a', c)
               end
             | None =>
               match isSetSecret r with
               | Some (q, true) =>
                 _ <- yield (getRandomBytes 0); (* needed for compiler limitation *)
                 rec (Some (q,0), sendinfo, None, bs, FromSetSecret, c)
               | Some (q, false) =>
                 _ <- yield (getRandomBytes 0); (* needed for compiler limitation *)
                 rec (recvinfo, Some (q,0), None, bs, FromSetSecret, c)
               | None =>
                 a' <- yield r;
                   rec (recvinfo, sendinfo, None, bs, a', c)
               end
             end
           end
         end
       | Some (mtype, bocont) =>
         if Nat.ltb (Blength bs) 5 then
           bs' <- yield RecvData $ tt;
           rec (recvinfo, sendinfo, Some (mtype, bocont), mconcat [bs; bs'], a, c)
         else
           _ <- yield (getRandomBytes 0); (* needed for compiler limitation *)
           let (hd,rest) := Bsplit 5 bs in
           match decodeHeader hd with
           | inl al =>
             rec (recvinfo, sendinfo, None, rest, RetAlert (Alert_Fatal, al), c)
           | inr hdr =>
             let maxSize := match recvinfo with
                            | None => maxPlaintextSize
                            | Some _ => maxCiphertextSize
                            end
             in
             if Nat.ltb maxSize (hdReadLen hdr) then
               rec (recvinfo, sendinfo, None, empty, RetAlert (Alert_Fatal, RecordOverflow), c)
             else if Nat.ltb (Blength rest) (hdReadLen hdr) then
               bs' <- yield RecvData $ tt;
               rec (recvinfo, sendinfo, Some (mtype, bocont), mconcat [bs; bs'], a, c)
             else
               let (msg,rest') := Bsplit (hdReadLen hdr) rest in
               if CProtocolType_beq CProtocolType_ChangeCipherSpec (hdProtocolType hdr) then
                 rec (recvinfo, sendinfo, Some (mtype, bocont), rest', a, c)
               else
                 oa' <<- decode bocont hdr msg mtype recvinfo;
                 match oa' with
                 | None =>
                   rec (recvinfo, sendinfo, Some (mtype, bocont), rest', a, c)
                 | Some (inr a') =>
                   match recvinfo with
                   | Some (q, num) =>
                     rec (Some (q, S num), sendinfo, None, rest', a', c)
                   | None => rec (None, sendinfo, None, rest', a', c)
                   end
                 | Some (inl (b,cont)) =>
                   match recvinfo with
                   | Some (q, num) =>
                     rec (Some (q, S num), sendinfo, Some (mtype, (b,Some cont)), rest', a, c)
                   | None =>
                     rec (recvinfo, sendinfo, Some (mtype, (b,Some cont)), rest', a, c)
                   end
                 end
           end
       end
     end)
    fuel (None, None, None, empty, inhabitant, coro)).

Inductive GenForall2_prod_r (A A1 A2 : Set)(R : A1 -> A2 -> Prop) : A * A1 -> A * A2 -> Prop :=
  GenForall2_prod_r_rule : forall a x1 x2, R x1 x2 -> GenForall2_prod_r A A1 A2 R (a,x1) (a,x2).

Program Instance prod_r_HasGenForall2 (A:Set) : HasGenForall2 (prod A) :=
  { GenForall2 := GenForall2_prod_r A }.

Program Instance id_HasGenForall2 : HasGenForall2 (fun A:Set => A) :=
  { GenForall2 := fun A1 A2 R => R }.

Opaque doHandshake_derive.

Parameter dummy_Error : TLSError.

Instance ParseResult_Inhabit (A:Set) : Inhabit (ParseResult A) :=
  { inhabitant := PError _ dummy_Error }.

Instance RecvType_Inhabit : Inhabit RecvType :=
  { inhabitant := RClientHello }.

Instance ternary_Inhabit2 (A B C:Set) `{ Inhabit B } : Inhabit (ternary A B C) :=
  { inhabitant := tnr2 inhabitant }.

Instance ternary_Inhabit3 (A B C:Set) `{ Inhabit C } : Inhabit (ternary A B C) :=
  { inhabitant := tnr3 inhabitant }.
Opaque doHandshake_step.
Definition readWrite_derive :
  { state & { step &
              forall fuel certs priv,
                { init | @equiv_coro _ _ _ _ _ state step init (readWrite fuel certs priv) } } }.
Proof.
  do 3 eexists.
  
  lazymatch goal with
    |- ?x => assert x
  end.
  unfold decode.
  intros.
  Time unshelve derive (tt,fuel,certs,priv); intros; exact inhabitant.
  lazymatch goal with
    |- @equiv_coro _ _ _ _ _ ?state ?step _ _ =>
    assert Set;
      [ pose state as st; transparent_abstract (exact st) using readWrite_state |];
    assert (step_type (const_yield args_tls) (const_yield rets_tls) (option string) readWrite_state);
    pose step as stp
  end.
  transparent_abstract (exact stp) using readWrite_step.
  Time Admitted.
(*
  unfold decode.
  unshelve derive (tt,fuel,certs,priv); intros; exact inhabitant.
Time Defined.
*)
Inductive eff_conn := accept | perform | receive | skip.


Definition args_conn (e : eff_conn) :=
  match e with
  | accept => unit
  | perform => string * args_tls
  | receive => unit
  | skip => unit
  end.

Definition rets_conn (e : eff_conn) :=
  match e with
  | accept => option string
  | perform => rets_tls
  | receive => option (string * rets_tls)
  | skip => unit
  end.

Notation "r <- ef a ; p" :=
  (@Eff eff_conn args_conn rets_conn _ ef a (fun r => p))
    (at level 100, ef at level 0, right associativity).
(*
Definition readWrite_step :=
  projT1 (projT2 readWrite_derive).
*)
Axiom readWrite_equiv : forall fuel certs keys,
  equiv_coro readWrite_step (inl (tt,fuel,certs,keys)) (readWrite fuel certs keys) (*:=
  proj2_sig (projT2 (projT2 readWrite_derive) fuel certs keys)*).

Hint Resolve readWrite_equiv : equivc.

Definition isSetPSK (x : args_tls) :=
  match x with
  | setPSK a => Some a
  | _ => None
  end.

Definition isSessionResume (x : args_tls) :=
  match x with
  | sessionResume a => Some a
  | _ => None
  end.

Definition isRecvDataOrClose (x : args_tls) :=
  match x with
  | recvData _ => Some tt
  | closeWith _ => Some tt
  | _ => None
  end.

Definition isSkip (x : args_tls) :=
  match x with
  | getRandomBytes n =>
    if Nat.eqb n 0 then
      Some tt
    else
      None
  | _ => None
  end.

Fixpoint take_max {A:Set} d (m' m : Map A) (ctx : Map A -> Map A) :=
  match m with
  | Leaf _ => (d, ctx m')
  | Node d' l r =>
    take_max d' l r (fun x => ctx (Node d m' x))
  end.

Definition merge_map {A:Set}(l r : Map A) :=
  match l with
  | Leaf _ => r
  | Node d l' r' =>
    let (d', m) := take_max d l' r' (fun x => x) in
    Node d' m r
  end.

Fixpoint lookupAndDelete' {A : Set} key (m : Map A) (ctx : Map A -> Map A) :=
  match m with
  | Leaf _ => (None, ctx (Leaf _))
  | Node (k,v) l r =>
    match compareString key k with
    | Eq => (Some v, ctx (merge_map l r))
    | Lt => lookupAndDelete' key l (fun x => ctx (Node (k,v) x r))
    | Gt => lookupAndDelete' key r (fun x => ctx (Node (k,v) l x))
    end
  end.

Definition lookupAndDelete {A : Set} key (m : Map A) :=
  lookupAndDelete' key m (fun x => x).

Opaque readWrite_step.

Definition Start := recvPacket RCCS.

Definition main_loop fuel fuel' fuel'' certs keys :=
  nat_rect_nondep
    (fun _ => Return (@None unit))
    (fun _ rec maps =>
       let (m,coros) := maps : Map SessionData * Map (coro_type readWrite_step) in
       osa <- accept tt;
         match osa with
         | Some sa =>
           pipe (readWrite fuel' certs keys : coro_type readWrite_step)
                (fun c =>
(*                   ef <- resume c $ inhabitant;*)
                   _ <- perform (sa, Start);
                   let coros' := insert sa c coros in
                   rec (m, coros'))
         | None =>
           osar <- receive tt;
           match osar with
           | None => rec (m,coros)
           | Some (sa,r) =>
             let ocoro := bsearch sa coros in
             coro <~ ifSome ocoro {{ rec (m,coros) }}
             nat_rect_nondep
               (fun mcoro => Return None)
               (fun _ rec_inner rmcoro =>
                  let (rm,coro) := (rmcoro : rets_tls * Map SessionData * coro_type readWrite_step) in
                  let (r,m) := (rm : rets_tls * Map SessionData) in
                  ef <- resume coro $ r;
                  match isSetPSK ef with
                  | Some (sid,sess) =>
                    let m' := insert sid sess m in
                    _ <- skip tt;
                      rec_inner (FromSetPSK,m', coro)
                  | None =>
                    match isSessionResume ef with
                    | Some sid =>
                      let (sess,m') := lookupAndDelete sid m in
                      _ <- skip tt;
                      rec_inner (FromSessionResume sess, m', coro)
                    | None =>
                      match isRecvDataOrClose ef with
                      | Some _ =>
                        _ <- perform (sa,ef);
                        let coros' := replace_map sa coro coros in
                        rec (m, coros')
                      | None =>
                        r <- perform (sa,ef);
                        rec_inner (r, m, coro)
                      end
                    end
                  end)
               fuel'' (r, m, coro)
           end
         end)
    fuel (Leaf _, Leaf _).

Parameter certs_dummy : CertificateChain.
Parameter privkey_dummy : PrivateKey.

Instance CertificateChain_Inhabit : Inhabit CertificateChain :=
  { inhabitant := certs_dummy }.

Instance PrivateKey_Inhabit : Inhabit PrivateKey :=
  { inhabitant := privkey_dummy }.

Definition lift_conn A B(e : eff_conn)(a : rets_conn e -> A + option B) e0
  : rets_conn e0 -> A + option B :=
  match
  e as e1
  return ((rets_conn e1 -> A + option B) -> rets_conn e0 -> A + option B)
  with
  | accept =>
    fun a0 : rets_conn accept -> A + option B =>
      match e0 as e1 return (rets_conn e1 -> A + option B) with
      | accept => a0
      | _ => fun _ => inr None
      end
  | perform =>
    fun a0 : rets_conn perform -> A + option B =>
      match e0 as e1 return (rets_conn e1 -> A + option B) with
      | perform => a0
      | _ => fun _ => inr None
      end
  | receive =>
    fun a0 : rets_conn receive -> A + option B =>
      match e0 as e1 return (rets_conn e1 -> A + option B) with
      | receive => a0
      | _ => fun _ => inr None
      end
  | skip =>
    fun a0 : rets_conn skip -> A + option B =>
      match e0 as e1 return (rets_conn e1 -> A + option B) with
      | skip => a0
      | _ => fun _ => inr None
      end
  end a.

Instance eff_conn_is_eff : is_eff eff_conn :=
  {| args := args_conn;
    rets := rets_conn;
    lift_eff := lift_conn |}.
Opaque inhabitant.

Instance CPacket_Inhabit : Inhabit CPacket :=
  { inhabitant := PChangeCipherSpec }.

Parameter pubkey_dummy : PublicKey.
Parameter hashsig_dummy : HashAndSignatureAlgorithm.
Parameter gpub_dummy : GroupPublic.
Parameter sd_dummy : SessionData.

Instance PublicKey_Inhabit : Inhabit PublicKey :=
  { inhabitant := pubkey_dummy }.
Instance HashAndSignatureAlgorithm_Inhabit : Inhabit HashAndSignatureAlgorithm :=
  { inhabitant := hashsig_dummy }.
Instance GroupPublic_Inhabit : Inhabit GroupPublic :=
  {inhabitant := gpub_dummy }.
Instance SessionData_Inhabit : Inhabit SessionData :=
  { inhabitant := sd_dummy }.

Definition main_loop_derive  :
  { state & { step & forall fuel fuel' fuel'' certs keys,
                { init | @equiv _ _ _ _ state step init (main_loop fuel fuel' fuel'' certs keys) } } }.
Proof.
  do 3 eexists.
  Time derive (tt,fuel,fuel',fuel'',certs,keys).
  Grab Existential Variables.
  all: intros; exact inhabitant.
Time Defined.

Transparent doHandshake_step readWrite_step.

Definition main_loop_step := Eval cbv [projT1 projT2 main_loop main_loop_derive] in (projT1 (projT2 (main_loop_derive))).

Require Import extraction.ExtrHaskellString.

Extract Inductive unit => "()" [ "()" ].
Extract Inductive list => "([])" ["[]" "(:)"].
Extract Inductive nat => "GHC.Base.Int" ["0" "(Prelude.+) 1"] "(\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))".
Extract Inductive bool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"].
Extract Inductive sumbool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"].
Extract Inductive prod => "(,)"  [ "(,)" ].
Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].
Extract Inductive option => "GHC.Base.Maybe" ["GHC.Base.Just" "GHC.Base.Nothing"].
Extract Inductive Group => "T.Group" ["T.P256" "T.P384" "T.P521" "T.X25519"].
Extract Inductive KeyShare => "I.KeyShareEntry" ["I.KeyShareEntry"].
Extract Inductive CHandshake => "I.Handshake13" ["I.ClientHello13" "I.ServerHello13" "I.NewSessionTicket13" "I.EndOfEarlyData13" "I.EncryptedExtensions13" "I.CertRequest13" "I.Certificate13" "I.CertVerify13" "I.Finished13" "I.KeyUpdate13"].
Extract Inductive CPacket => "I.Packet13" ["I.Handshake13" "I.Alert13" "I.ChangeCipherSpec13" "I.AppData13"].
Extract Inductive CServerRandom => "I.ServerRandom" ["I.ServerRandom"].
Extract Inductive CClientRandom => "I.ClientRandom" ["I.ClientRandom"].
Extract Inductive SessionData => "I.SessionData" ["I.SessionData"].
Extract Inductive SessionFlag =>"I.SessionFlag" ["I.SessionEMS"].
Extract Inductive PskIdentity => "I.PskIdentity" ["I.PskIdentity"].
Extract Inductive PreSharedKey => "I.PreSharedKey" ["I.PreSharedKeyClientHello" "I.PreSharedKeyServerHello"].
Extract Inductive PskKexMode => "I.PskKexMode" ["I.PSK_KE" "I.PSK_DHE_KE"].
Extract Inductive HashAlgorithm => "I.HashAlgorithm" ["I.HashNone" "I.HashMD5" "I.HashSHA1" "I.HashSHA224" "I.HashSHA256" "I.HashSHA384" "I.HashSHA512" "I.HashIntrinsic" "I.HashOther"].
Extract Inductive SignatureAlgorithm => "I.SignatureAlgorithm" ["I.SignatureAnonymous" "I.SignatureRSA" "I.SignatureDSS" "I.SignatureECDSA" "I.SignatureRSApssRSAeSHA256" "I.SignatureRSApssRSAeSHA384" "I.SignatureRSApssRSAeSHA512" "I.SignatureEd25519" "I.SignatureEd448" "I.SignatureRSApsspssSHA256" "I.SignatureRSApsspssSHA384" "I.SignatureRSApsspss512" "I.SignatureOther"].
Extract Inductive ServerNameType => "I.ServerNameType" ["I.ServerNameHostName" "I.ServerNameOther"].
Extract Inductive ServerName => "I.ServerName" ["I.ServerName"].
Extract Inductive AlertLevel => "I.AlertLevel" ["I.AlertLevel_Warning" "I.AlertLevel_Fatal"].
Extract Inductive AlertDescription => "I.AlertDescription"
[ "I.CloseNotify"
  "I.UnexpectedMessage"
  "I.BadRecordMac"
  "I.DecryptionFailed"
  "I.RecordOverflow"
  "I.DecompressionFailure"
  "I.HandshakeFailure"
  "I.BadCertificate"
  "I.UnsupportedCertificate"
  "I.CertificateRevoked"
  "I.CertificateExpired"
  "I.CertificateUnknown"
  "I.IllegalParameter"
  "I.UnknownCa"
  "I.AccessDenied"
  "I.DecodeError"
  "I.DecryptError"
  "I.ExportRestriction"
  "I.ProtocolVersion"
  "I.InsufficientSecurity"
  "I.InternalError"
  "I.InappropriateFallback"
  "I.UserCanceled"
  "I.NoRenegotiation"
  "I.MissingExtension"
  "I.UnsupportedExtension"
  "I.CertificateUnobtainable"
  "I.UnrecognizedName"
  "I.BadCertificateStatusResponse"
  "I.BadCertificateHashValue"
  "I.UnknownPskIdentity"
  "I.CertificateRequired"
  "I.NoApplicationProtocol"].
Extract Constant ProtocolType => "I.ProtocolType".
Extract Constant decodeRecord => "Helper.decodeRecord".
Extract Constant decodeHeader => "\bs  -> case I.decodeHeader bs of { Prelude.Right a -> Prelude.Right a ; Prelude.Left err -> Prelude.Left (snd (errorToAlert err)) }".
Extract Constant Certificate => "X.Certificate".
Extract Constant CertificateChain => "X.CertificateChain".
Extract Constant getCertificates => "\cch -> case cch of { X.CertificateChain certs -> Prelude.map X.getCertificate certs }".
Extract Constant Group_eq_dec => "(GHC.Base.==)".
Extract Constant Group_beq => "(GHC.Base.==)".
Extract Constant ExtensionRaw => "I.ExtensionRaw".
Extract Constant Session => "I.Session".
Extract Constant CipherID => "T.CipherID".
(*
Extract Constant Handshake13 => "I.Handshake13".
Extract Constant Packet13 => "I.Packet13".
*)
Extract Constant ByteString => "B.ByteString".
Extract Constant mconcat => "B.concat".
Extract Constant extensionEncode_KeyShare => "(\ks -> I.extensionEncode (I.KeyShareServerHello ks))".
Extract Constant extensionEncode_SupportedVersions =>
"(\v -> I.extensionEncode (I.SupportedVersionsServerHello v))".
Extract Constant Version => "T.Version".
Extract Constant TLS13 => "T.TLS13".
Extract Constant extensionRaw_KeyShare => "I.ExtensionRaw I.extensionID_KeyShare".
Extract Constant extensionRaw_SupportedVersions =>
"I.ExtensionRaw I.extensionID_SupportedVersions".
Extract Constant extension_SupportedGroups =>
"\exts -> case Helper.extensionLookup I.extensionID_NegotiatedGroups exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.NegotiatedGroups gs) -> GHC.Base.Just gs; _ -> GHC.Base.Nothing }".
Extract Constant extension_NegotiatedGroups =>
"\exts -> case Helper.extensionLookup I.extensionID_NegotiatedGroups exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.NegotiatedGroups gs) -> GHC.Base.Just gs; _ -> GHC.Base.Nothing }".
Extract Constant extension_KeyShare =>
"(\exts -> case Helper.extensionLookup I.extensionID_KeyShare exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.KeyShareClientHello kses) -> GHC.Base.return kses})".
Extract Constant serverGroups => "Helper.serverGroups".
Extract Constant changeCipherSpec => "\p -> case p of { I.ChangeCipherSpec13 -> GHC.Base.Just (); _ -> GHC.Base.Nothing }".
Extract Constant extension_SignatureAlgorithms =>
"(\exts -> case Helper.extensionLookup I.extensionID_SignatureAlgorithms exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.SignatureAlgorithms sas) -> GHC.Base.Just sas; _ -> GHC.Base.Nothing })".
Extract Constant extensionLookup_SignatureAlgorithms =>
"Helper.extensionLookup I.extensionID_SignatureAlgorithms".
Extract Constant extensionDecode_SignatureAlgorithms =>
"\exts -> case I.extensionDecode I.MsgTClientHello exts of { GHC.Base.Just (I.SignatureAlgorithms sas) -> GHC.Base.Just sas; _ -> GHC.Base.Nothing }".
Extract Constant defaultCertChain => "Helper.defaultCertChain".
Extract Constant empty => "B.empty".
Extract Constant PublicKey => "X.PubKey".
Extract Constant PrivateKey => "X.PrivKey".
Extract Constant hashWith => "Helper.hashWith".
(*Extract Constant makeCertVerify => "Helper.makeCertVerify".*)
Extract Constant Hash => "T.Hash".
Extract Constant Cipher => "T.Cipher".
Extract Constant cipherID => "T.cipherID".
Extract Constant CipherID_beq => "(GHC.Base.==)".
Extract Constant cipherHash => "T.cipherHash".
Extract Constant serverCiphers => "I.ciphersuite_13".
Extract Constant sniExt => "Helper.sniExt".
Extract Constant CryptoError => "I.CryptoError".
Extract Constant encodeGroupPublic => "I.encodeGroupPublic".
Extract Constant decodeGroupPublic => "\g bs -> case I.decodeGroupPublic g bs of { Prelude.Right a -> GHC.Base.Just a; _ -> GHC.Base.Nothing }".
Extract Constant ba_convert => "BA.convert".
Extract Constant hashDigestSize => "I.hashDigestSize".
Extract Constant Word8 => "Data.Word8.Word8".
Extract Constant Word8_beq => "(GHC.Base.==)".
Extract Constant b_replicate => "B.replicate".
Extract Constant w0 => "Data.Word8._nul".
Extract Constant hkdfExtract => "I.hkdfExtract".
Extract Constant hkdfExpandLabel => "I.hkdfExpandLabel".
Extract Constant s2b => "(\s -> B.pack (Prelude.map (\c -> Prelude.fromIntegral (Data.Char.ord c)) s))".
Extract Constant b2s => "(\b -> Prelude.map Data.ByteString.Internal.w2c (B.unpack b))".
Extract Constant GroupKey => "I.GroupKey".
Extract Constant GroupPublic => "I.GroupPublic".
Extract Constant hmac => "I.hmac".
Extract Constant ByteString_beq => "(GHC.Base.==)".
Extract Constant isDigitalSignaturePair => "I.isDigitalSignaturePair".
Extract Constant signatureCompatible13 => "I.signatureCompatible13".
Extract Constant certPubKey => "X.certPubKey".
Extract Constant Word32 => "Data.Word.Word32".
Extract Constant Word64 => "Data.Word.Word64".
Extract Constant Signature => "I.Signature".
Extract Constant KeyUpdate => "I.KeyUpdate".
Extract Constant Bsplit => "B.splitAt".
Extract Constant Blength => "B.length".
Extract Constant Hash_beq => "(GHC.Base.==)".
Extract Constant ExtensionRaw_PreSharedKey =>
"I.ExtensionRaw I.extensionID_PreSharedKey".
Extract Inductive TicketInfo => "T.TLS13TicketInfo" ["T.TLS13TicketInfo"].
Extract Constant encodeHandshake13 => "I.encodeHandshake13".
Extract Constant extension_PreSharedKey =>
"\exts -> Helper.extensionLookup I.extensionID_PreSharedKey exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello".
Extract Constant nat2Word32 => "Prelude.fromIntegral".
Extract Constant extension_PskKeyModes =>
"(\exts -> case Helper.extensionLookup I.extensionID_PskKeyExchangeModes exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.PskKeyExchangeModes ms) -> GHC.Base.return ms; GHC.Base.Nothing -> GHC.Base.return []})".
Extract Constant Btake => "B.take".
Extract Constant extensionEncode_PreSharedKey => "I.extensionEncode".
Extract Constant extensionEncode_SupportedVersionsServerHello => "\v -> I.extensionEncode (I.SupportedVersionsServerHello v)".
Extract Constant life => "172800".
Extract Constant Word64gt => "(Prelude.>)".
Extract Constant Word32le => "(Prelude.<=)".
Extract Constant w64_2000 => "2000".
Extract Constant extension_ServerName => "\exts -> Helper.extensionLookup I.extensionID_ServerName exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello".
Extract Constant Word64minus => "(Prelude.-)".
Extract Constant w32to64 => "Prelude.fromIntegral".
Extract Constant Word32minus => "(Prelude.-)".
Extract Constant maxCiphertextSize => "16384 Prelude.+ 256".
Extract Constant maxPlaintextSize => "16384".
Extract Constant bytes2w32 => "B.foldl' (\x y -> x Prelude.* 256 Prelude.+ Prelude.fromIntegral y) 0".
Extract Constant Version_beq => "(Prelude.==)".
Extract Constant Word64plus => "(Prelude.+)".
Extract Constant extension_SupportedVersionsCH => "\exts -> case Helper.extensionLookup I.extensionID_SupportedVersions exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of {GHC.Base.Just (I.SupportedVersionsClientHello vers) -> GHC.Base.Just vers; _ -> GHC.Base.Nothing }".
Extract Constant Word64max => "Prelude.max".
Extract Constant CompressionID => "T.CompressionID".
Extract Constant dummyCompressionID => "GHC.Base.undefined".
Extract Constant TLSError => "I.TLSError".
Extract Constant errorToAlert => "Helper.errorToAlert".
Extract Constant parseHandshakeRecord => "Helper.parseHandshakeRecord".
Extract Constant HandshakeType => "I.HandshakeType13".
Extract Constant parseHandshake => "Helper.parseHandshake".
Extract Constant messageHash00 => "B.pack [254,0,0]".
Extract Constant hrrRandom => "I.ServerRandom (B.pack [ 
    0xCF, 0x21, 0xAD, 0x74, 0xE5, 0x9A, 0x61, 0x11
  , 0xBE, 0x1D, 0x8C, 0x02, 0x1E, 0x65, 0xB8, 0x91
  , 0xC2, 0xA2, 0x11, 0x16, 0x7A, 0xBB, 0x8C, 0x5E
  , 0x07, 0x9E, 0x09, 0xE2, 0xC8, 0xA8, 0x33, 0x9C
  ])".
Extract Constant extensionEncode_KeyShareHRR => "\x -> I.extensionEncode (I.KeyShareHRR x)".
Extract Constant natToBytes => "\n -> B.pack [Prelude.fromIntegral n]".
Extract Constant dummyCCS => "B.pack [1]".
Extract Constant Header => "I.Header".
Extract Constant hdReadLen => "\x -> case x of { I.Header _ _ n -> Prelude.fromIntegral n }".
Extract Constant hdProtocolType => "\x -> case x of { I.Header t _ _ -> t }".
Extract Constant extension_ALPN => "\_ ->GHC.Base.Nothing".
Extract Inductive CProtocolType => "I.ProtocolType" ["I.ProtocolType_ChangeCipherSpec" "I.ProtocolType_Alert" "I.ProtocolType_Handshake" "I.ProtocolType_AppData" "I.ProtocolType_DeprecatedHandshake"].
Extract Inductive ParseResult => "I.GetResult" ["I.GotError" "I.GotPartial" "I.GotSuccess" "I.GotSuccessRemaining"].
Extract Constant pskkey => "Prelude.Nothing".

Require Extraction.
Extraction Language Haskell.

Extraction "TLS.hs" main_loop_step.
