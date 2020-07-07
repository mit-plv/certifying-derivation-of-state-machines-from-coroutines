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
                 
Definition clientHello (h : CPacket) :=
  match h with
  | PHandshake [HClientHello v (CRn rand) sess cipherIDs ext] =>
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
| close : unit -> args_tls
| sendData : CPacket * option (Hash * Cipher * ByteString * nat) -> args_tls
| getRandomBytes : nat -> args_tls
| recvData : unit -> args_tls
| groupGetPubShared : GroupPublic -> args_tls
| makeCertVerify : PublicKey * PrivateKey * HashAndSignatureAlgorithm * ByteString -> args_tls
| setSecret : Hash * Cipher * ByteString * bool -> args_tls
| sendPacket : CPacket -> args_tls
| recvPacket : unit + unit + unit + unit -> args_tls.

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
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromSetPSK r')))
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
  (Eff yield (close a)
       (fun r => p))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvClientHello' $ a ; p" :=
  (Eff yield (recvPacket (inr a))
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (sendPacket (PAlert [al]))
                                                  (fun _ => Return inhabitant))
                                   (Return inhabitant) (retAlert r'))
                    (fromRecvClientHello r')))
       (at level 100, right associativity).

Notation "r <- 'yield' 'RecvData' $ a ; p" :=
  (Eff yield (recvData a)
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (sendPacket (PAlert [al]))
                                                  (fun _ => Return inhabitant))
                                   (Return inhabitant) (retAlert r'))
                    (fromRecvData r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvFinished' $ a ; p" :=
  (Eff yield (recvPacket (inl (inl (inr a))))
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (sendPacket (PAlert [al]))
                                                  (fun _ => Return inhabitant))
                                   (Return inhabitant) (retAlert r'))
                    (fromRecvFinished r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvCCS' $ a ; p" :=
  (Eff yield (recvPacket (inl (inr a)))
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (sendPacket (PAlert [al]))
                                                  (fun _ => Return inhabitant))
                                   (Return inhabitant) (retAlert r'))
                    (fromRecvCCS r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvAppData' $ a ; p" :=
  (Eff yield (recvPacket (inl (inl (inl a))))
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (sendPacket (PAlert [al]))
                                                  (fun _ => Return inhabitant))
                                   (Return inhabitant) (retAlert r'))
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
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromSetSecret r')))
    (at level 100, right associativity).

(*

Notation "r <- 'yield' 'SetPSK' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl a)))))))))))
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromSetPSK r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'SessionResume' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr a)))))))))))
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromSessionResume r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'GetCurrentTime' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr a))))))))))
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromGetCurrentTime r')))
       (at level 100, right associativity).

Notation "r <- 'yield' 'Close' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inl (inl (inl (inr a)))))))))
       (fun r => p))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvClientHello' $ a ; p" :=
  (Eff yield (inr (inr a))
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (inl (inr (PAlert [al])))
                                                  (fun _ => Return inhabitant))
                                   (Return inhabitant) (retAlert r'))
                    (fromRecvClientHello r')))
       (at level 100, right associativity).

Notation "r <- 'yield' 'RecvData' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inr a))))))
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (inl (inr (PAlert [al])))
                                                  (fun _ => Return inhabitant))
                                   (Return inhabitant) (retAlert r'))
                    (fromRecvData r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvFinished' $ a ; p" :=
  (Eff yield (inr (inl (inl (inr a))))
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (inl (inr (PAlert [al])))
                                                  (fun _ => Return inhabitant))
                                   (Return inhabitant) (retAlert r'))
                    (fromRecvData r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvCCS' $ a ; p" :=
  (Eff yield (inr (inl (inr a)))
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (inl (inr (PAlert [al])))
                                                  (fun _ => Return inhabitant))
                                   (Return inhabitant) (retAlert r'))
                    (fromRecvCCS r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvAppData' $ a ; p" :=
  (Eff yield (inr (inl (inl (inl a))))
       (fun r' => option_branch
                    (fun r => p)
                    (option_branch (fun al => Eff yield (inl (inr (PAlert [al])))
                                                  (fun _ => Return inhabitant))
                                   (Return inhabitant) (retAlert r'))
                    (fromRecvAppData r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'GetRandomBytes' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inl (inr a)))))))
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromGetRandomBytes r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'SendPacket' $ a ; p" :=
  (Eff yield (inl (inr a))
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromSendPacket r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'GroupGetPubShared' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inr a)))))
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromGroupGetPubShared r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'MakeCertVerify' $ a ; p" :=
  (Eff yield (inl (inl (inl (inr a))))
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromMakeCertVerify r')))
    (at level 100, right associativity).

Notation "r <- 'yield' 'SetSecret' $ a ; p" :=
  (Eff yield (inl (inl (inr a)))
       (fun r' => option_branch (fun r => p) (Return inhabitant) (fromSetSecret r')))
    (at level 100, right associativity).
*)

Instance sigT_rets_inhabit : Inhabit rets_tls :=
  { inhabitant := FromSetPSK }.

Instance sigT_args_inhabit : Inhabit args_tls :=
  { inhabitant := close tt }.

Parameter ProtocolType : Set.
Inductive Header := header : ProtocolType -> Version -> nat -> Header.

Definition hdReadLen hd :=
  match hd with
  | header _ _ n => n
  end.

Parameter decodeHeader : ByteString -> option Header.
Parameter decodeRecord : Header -> option (Hash * Cipher * ByteString * nat) -> ByteString -> AlertLevel * AlertDescription + CPacket.
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
  Def (fun al => (_ <- yield SendPacket $ PAlert [(Alert_Fatal, al)];
                 _ <- yield Close $ tt;
                 Return None) : t (const_yield args_tls) (const_yield rets_tls) (option (list ByteString * ClientHelloMsg * KeyShare))) (fun alert =>
  let chHashed := hashWith hash [chEncoded'] in

  let clientGroups :=
      match extension_NegotiatedGroups ch.(chExt) with
      | Some gs => gs
      | None => []
      end
  in
  let possibleGroups := intersect serverGroups clientGroups in
  match hd_error possibleGroups with
  | None => _ <- yield SendPacket $ (PAlert [(Alert_Fatal, HandshakeFailure)]);
            _ <- yield Close $ tt; Return None
  | Some g =>
    let serverKeyShare := extensionEncode_KeyShareHRR g in
    let selectedVersion := extensionEncode_SupportedVersionsServerHello TLS13 in
    let extensions := [extensionRaw_KeyShare serverKeyShare;
                         extensionRaw_SupportedVersions selectedVersion]
    in
    let hrr := HServerHello hrrRandom ch.(chSess) (cipherID cipher) extensions in
    _ <- yield SendPacket $ PHandshake [hrr];
    _ <- yield SendPacket $ PChangeCipherSpec;
    d <- yield RecvClientHello $ tt;
    let (chEncoded, chnew) := (d : ByteString * ClientHelloMsg) in
    let transcript := [messageHash00; natToBytes (Blength chHashed); chHashed; chEncoded] in
    keyShares <~ ifSome extension_KeyShare chnew.(chExt)
      {{ _ <- yield SendPacket $ (PAlert [(Alert_Fatal, IllegalParameter)]);
         _ <- yield Close $ tt;
         Return None
      }}
    match hd_error keyShares with
    | None => _ <- yield SendPacket $ (PAlert [(Alert_Fatal, IllegalParameter)]);
              _ <- yield Close $ tt;
              Return None
    | Some keyShare =>
      if negb (Group_beq g keyShare.(ksGroup)) then
        _ <- yield SendPacket $ (PAlert [(Alert_Fatal, IllegalParameter)]);
        _ <- yield Close $ tt;
        Return None
      else
        Return (Some (transcript, chnew, keyShare))
    end
  end).

Parameter extension_SupportedVersionsCH : list ExtensionRaw -> option (list Version).
Parameter bytes2w32 : ByteString -> Word32.
Parameter life : Word32.

Definition doHandshake (fuel:nat) (cch: CertificateChain)(pr: PrivateKey)(_: rets_tls)
  : t (const_yield args_tls) (const_yield rets_tls) unit := Eval unfold option_branch in
  Def (fun al => _ <- yield SendPacket $ PAlert [(Alert_Fatal, al)];
                 _ <- yield Close $ tt;
                 Return tt) (fun alert =>
  let certs := getCertificates cch in
  d' <- yield RecvClientHello $ tt;
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
  o <<- match findKeyShare keyShares serverGroups with
        | None => Return None (* doHelloRetryRequest chEncoded se usedHash cipher*)
        | Some keyShare =>
          Return (Some ([chEncoded], se, keyShare))
        end;
  d <~ ifSome o
    {{ alert IllegalParameter }}
  let (tch, keyShare) := (d : list ByteString * ClientHelloMsg * KeyShare) in
  let (transcript', ch) := (tch : list ByteString * ClientHelloMsg) in
  let chExts := chExt ch in
  cpub <~ ifSome decodeGroupPublic (ksGroup keyShare) (ksData keyShare)
    {{ alert IllegalParameter }}
  mecdhePair <- yield GroupGetPubShared $ cpub;
  ecdhePair <~ ifSome mecdhePair
    {{ alert IllegalParameter (*_ <- yield SendPacket $ (PAlert [(Alert_Fatal, IllegalParameter)]);
(*       _ <- yield Close $ tt;*)
       Return tt *) }}
  let wspub := encodeGroupPublic (fst ecdhePair) in
  let ecdhe := ba_convert (snd ecdhePair) in
  let serverKeyShare := {| ksGroup := ksGroup keyShare; ksData := wspub |} in
  let osni := chooseServerName chExts in
  let eExts := match osni with
               | None => []
               | Some _ => [sniExt]
               end
  in
  
  (* sendServerHello *)
  let ks := extensionEncode_KeyShare serverKeyShare in
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
  srand <- yield GetRandomBytes $ 32;
  shEncoded <- yield SendPacket $
            (PHandshake [HServerHello (SR srand) sess (cipherID cipher) extensions']);

  (* calculate handshake secrets *)
  let hCh := hashWith usedHash [chEncoded; shEncoded] in
  let clientEarlySecret := hkdfExpandLabel usedHash earlySecret (s2b "c e traffic") hCh hsize in
  
  let handshakeSecret := hkdfExtract usedHash (hkdfExpandLabel usedHash earlySecret (s2b "derived") (hashWith usedHash [s2b ""]) hsize) ecdhe in
  let clientHandshakeSecret := hkdfExpandLabel usedHash handshakeSecret (s2b "c hs traffic") hCh hsize in
  let serverHandshakeSecret := hkdfExpandLabel usedHash handshakeSecret (s2b "s hs traffic") hCh hsize in

  ccsEncoded <- yield SendPacket $ PChangeCipherSpec;
  _ <- yield SetSecret $ (usedHash, cipher, serverHandshakeSecret, false);
  extEncoded <- yield SendPacket $
             (PHandshake [HEncryptedExtensions eExts]);
  let sendCertAndVerify :=
      let transcript := (transcript' ++ [shEncoded; extEncoded])%list in
      match binderInfo with
      | Some _ => Return (Some transcript)
      | None =>
        hashSigs <~ ifSome extension_SignatureAlgorithms chExts
          {{ _ <- yield SendPacket $ PAlert [(Alert_Fatal, MissingExtension)];
             _ <- yield Close $ tt;
             Return None }}
        pubhs <~ ifSome decideCredInfo pr certs hashSigs
          {{ _ <- yield SendPacket $ (PAlert [(Alert_Fatal,HandshakeFailure)]);
             _ <- yield Close $ tt;
             Return None }}
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
  transcript <~ ifSome otranscript {{ Return tt }}
  
  let hashed' := hashWith (cipherHash cipher) transcript in
  finEncoded <- yield SendPacket $
             (PHandshake [HFinished (makeVerifyData usedHash serverHandshakeSecret hashed')]);
  sfSentTime <- yield GetCurrentTime $ tt;
  let hashed'' := hashWith (cipherHash cipher) (transcript ++ [finEncoded]) in
  let applicationSecret := hkdfExtract usedHash (hkdfExpandLabel usedHash handshakeSecret (s2b "derived") (hashWith usedHash [s2b ""]) hsize) zero in
  let clientApplicationSecret := hkdfExpandLabel usedHash applicationSecret (s2b "c ap traffic") hashed'' hsize in
  let serverApplicationSecret := hkdfExpandLabel usedHash applicationSecret (s2b "s ap traffic") hashed'' hsize in

  _ <- yield RecvCCS $ tt;
  _ <- yield SetSecret $ (usedHash, cipher, clientHandshakeSecret, true);
  fin <- yield RecvFinished $ tt;
  cfRecvTime <- yield GetCurrentTime $ tt;

  (* calculate application secrets *)
  let hashed''' := hashWith (cipherHash cipher) (transcript ++ [finEncoded; encodeHandshake13 (HFinished fin)]) in
  let resumptionMasterSecret := hkdfExpandLabel usedHash applicationSecret (s2b "res master") hashed''' hsize in
  if ByteString_beq fin (makeVerifyData usedHash clientHandshakeSecret hashed'') then
    nonce <- yield GetRandomBytes $ 32;
    bAgeAdd <- yield GetRandomBytes $ 4;
    let bAdd := bytes2w32 bAgeAdd in
    let tinfo := {| lifetime := life;
                    ageAdd := bAdd;
                    txrxTime := cfRecvTime;
                    estimatedRTT := Some (Word64minus cfRecvTime sfSentTime) |}
    in
    let pac := PHandshake [HNewSessionTicket life (bytes2w32 bAgeAdd) nonce (s2b "TestSession") []] in
    _ <- yield SetPSK $ ("TestSession",
                         {| sessionVersion := TLS13;
                            sessionCipher := cipherID cipher;
                            sessionGroup := None;
                            sessionTicketInfo := Some tinfo;
                            sessionCompression := dummyCompressionID;
                            sessionClientSNI := osni;
                            sessionSecret := hkdfExpandLabel usedHash resumptionMasterSecret (s2b "resumption") (s2b "0") hsize;
                            sessionALPN := None;
                            sessionMaxEarlyDataSize := 5;
                            sessionFlags := []
                         |});
    _ <- yield SetSecret $ (usedHash, cipher, serverApplicationSecret, false);
    _ <- yield SetSecret $ (usedHash, cipher, clientApplicationSecret, true);
    _ <- yield SendPacket $ pac;
    _ <- yield Close $ tt;
    Return tt
    (*
    nat_rect_nondep
      (fun _ => Return tt)
      (fun _ rec _ =>
         data <- yield RecvAppData $ (Some (usedHash, cipher, clientApplicationSecret));
         x <- yield SendPacket $ (PAppData13 (mconcat ([s2b ("HTTP/1.1 200 OK" ++ CR ++ LF ++ "Content-Type: text/plain" ++ CR ++ LF ++ CR ++ LF ++ "Hello, "); data; s2b ("!" ++ CR ++ LF)])), Some (usedHash, cipher, serverApplicationSecret));
         rec tt)
      fuel tt
*)
  else
    _ <- yield SendPacket $ (PAlert [(Alert_Fatal, DecryptError)]);
    _ <- yield Close $ tt; 
    Return tt)
.

Opaque replicate.

Definition doHandshake_derive :
  { state & { step &
              forall fuel certs priv,
                { init | @equiv_coro _ _ _ _ _ state step init (doHandshake fuel certs priv) } } }.
Proof.
  do 3 eexists.
  unfold doHandshake.
  Set Ltac Profiling.
  derive_coro (tt,fuel,certs,priv).
  Show Ltac Profile.
  Grab Existential Variables.
  all: exact inhabitant.
Time Defined.

Definition doHandshake_step := projT1 (projT2 doHandshake_derive).

Definition doHandshake_equiv fuel certs keys :
  equiv_coro doHandshake_step (inl (tt,fuel,certs,keys)) (doHandshake fuel certs keys) :=
  proj2_sig (projT2 (projT2 doHandshake_derive) fuel certs keys).

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

Definition decode header bs (s:unit+unit+unit+unit) o : t (const_yield args_tls) (const_yield rets_tls) rets_tls :=
  match decodeRecord header o bs with
  | inl al => Return (RetAlert al)
  | inr r => 
    match s with
    | inr _ =>
      match clientHello r with
      | None => Return (RetAlert (Alert_Fatal, UnexpectedMessage))
      | Some c => Return (FromRecvClientHello (bs,c))
      end
    | inl (inr _) =>
      match changeCipherSpec r with
      | None => Return (RetAlert (Alert_Fatal, UnexpectedMessage))
      | Some _ => Return FromRecvCCS
      end
    | inl (inl (inr _)) =>
      match handshake r with
      | None => Return (RetAlert (Alert_Fatal, UnexpectedMessage))
      | Some h =>
        match finished h with
        | None => Return (RetAlert (Alert_Fatal, UnexpectedMessage))
        | Some f => Return (FromRecvFinished f)
        end
      end
    | inl (inl (inl _)) =>
      match appData r with
      | None => Return (RetAlert (Alert_Fatal, UnexpectedMessage))
      | Some a => Return (FromRecvAppData a)
      end
    end
  end.

(*
Definition seqNum (current : ByteString * nat)(key : ByteString) :=
  let (k,n) := current in
  if ByteString_beq key k key then
    (k, S n, n)
  else
    (key, 1, 0).
*)
(*
  (fix aux pre tbl :=
     match tbl with
     | [] => ((key,1)::pre, 0)
     | (k,n)::rest =>
       if ByteString_beq k key then
         ((k,S n)::pre ++ tbl, n)%list
       else aux ((k,n)::pre) rest
     end) [] tbl.
*)

Parameter maxCiphertextSize : nat.

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

Definition readWrite fuel certs keys(_: rets_tls) : t (const_yield _) (const_yield rets_tls) (option String.string) :=
  pipe (doHandshake fuel certs keys) (fun coro : coro_type doHandshake_step =>
  nat_rect_nondep
    (fun _ => Return None)
    (fun _ rec (ctx: option (Hash * Cipher * ByteString * nat) * option (Hash * Cipher * ByteString * nat) * option (unit+unit+unit+unit) * ByteString * rets_tls * coro_type doHandshake_step) =>
       _ <- yield (getRandomBytes 0); (* needed for compiler limitation *)
       match ctx with
       | (recvinfo,sendinfo,omtype,bs,a,c) =>
       match omtype with
       | None =>
         r <- resume c $ a;
         match isRecvPacket r with
         | Some mtype =>
           rec (recvinfo, sendinfo, Some mtype, bs, a, c)
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
             match isSetSecret r with
             | Some (q, true) =>
               rec (Some (q,0), sendinfo, None, bs, FromSetSecret, c)
             | Some (q, false) =>
               rec (recvinfo, Some (q,0), None, bs, FromSetSecret, c)
             | None =>
               a' <- yield r;
                 rec (recvinfo, sendinfo, None, bs, a', c)
             end
           end
         end
       | Some mtype =>
         if Nat.ltb (Blength bs) 5 then
           bs' <- yield RecvData $ tt;
           rec (recvinfo, sendinfo, Some mtype, mconcat [bs; bs'], a, c)
         else
           let (hd,rest) := Bsplit 5 bs in
           match decodeHeader hd with
           | None => rec (recvinfo, sendinfo, None, rest, RetAlert (Alert_Fatal, DecodeError), c)
           | Some hdr =>
             if Nat.ltb maxCiphertextSize (hdReadLen hdr) then
               rec (recvinfo, sendinfo, None, empty, RetAlert (Alert_Fatal, RecordOverflow), c)
             else if Nat.ltb (Blength rest) (hdReadLen hdr) then
               bs' <- yield RecvData $ tt;
               rec (recvinfo, sendinfo, Some mtype, mconcat [bs; bs'], a, c)
             else
             let (msg,rest') := Bsplit (hdReadLen hdr) rest in
             a' <<- decode hdr msg mtype recvinfo;
             match recvinfo with
             | Some (q, num) =>
               rec (Some (q, S num), sendinfo, None, rest', a', c)
             | None => rec (None, sendinfo, None, rest', a', c)
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

Definition readWrite_derive :
  { state & { step &
              forall fuel certs priv,
                { init | @equiv_coro _ _ _ _ _ state step init (readWrite fuel certs priv) } } }.
Proof.
  do 3 eexists.
  unfold decode.
  Set Ltac Profiling.
  unshelve derive (tt,fuel,certs,priv); exact inhabitant.
  Show Ltac Profile.
Time Defined.

Inductive eff_conn := newAccept | perform | receive.


Definition args_conn (e : eff_conn) :=
  match e with
  | newAccept => unit
  | perform => string * args_tls
  | receive => unit
  end.

Definition rets_conn (e : eff_conn) :=
  match e with
  | newAccept => option string
  | perform => unit
  | receive => option (string * rets_tls)
  end.

Notation "r <- ef a ; p" :=
  (@Eff eff_conn args_conn rets_conn _ ef a (fun r => p))
    (at level 100, ef at level 0, right associativity).

Definition readWrite_step :=
  projT1 (projT2 readWrite_derive).

Definition readWrite_equiv fuel certs keys :
  equiv_coro readWrite_step (inl (tt,fuel,certs,keys)) (readWrite fuel certs keys) :=
  proj2_sig (projT2 (projT2 readWrite_derive) fuel certs keys).

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

Definition main_loop fuel fuel' certs keys := Eval unfold option_branch in
  nat_rect_nondep
    (fun _ => Return (@None unit))
    (fun _ rec ormaps =>
       let (orm,coros) := ormaps : option (string * rets_tls) * Map SessionData * Map (coro_type readWrite_step) in
       let (or,m) := orm : option (string * rets_tls) * Map SessionData in
       osa <- newAccept tt;
         match osa with
         | Some sa =>
           pipe (readWrite fuel' certs keys : coro_type readWrite_step)
                (fun c =>
                   ef <- resume c $ inhabitant;
                     _ <- perform (sa, ef);
                     let coros' := insert sa c coros in
                     rec (or, m, coros'))
         | None =>
           osar <<-
               match or with
               | Some p => Return (Some p)
               | None =>
                 o <- receive tt;
                 match o with
                 | None => Return None
                 | Some p => Return (Some p)
                 end
               end;
           match osar with
           | None => rec (None, m, coros)
           | Some (sa,r) =>
             let ocoro := bsearch sa coros in
             coro <~ ifSome ocoro {{ Return None }}
             ef <- resume coro $ r;
             let coros' := replace_map sa coro coros in
             match isSetPSK ef with
             | Some (sid,sess) =>
               let m' := insert sid sess m in
               rec (Some (sa, FromSetPSK), m', coros')
             | None =>
               match isSessionResume ef with
               | Some sid =>
                 let (sess,m') := lookupAndDelete sid m in
                 rec (Some (sa, (FromSessionResume sess)), m', coros')
               | None =>
                 _ <- perform (sa,ef);
                 rec (None, m, coros')
               end
             end
           end
         end)
    fuel (None, Leaf _, Leaf _).

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
  | newAccept =>
    fun a0 : rets_conn newAccept -> A + option B =>
      match e0 as e1 return (rets_conn e1 -> A + option B) with
      | newAccept => a0
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

Ltac sum_match_fun_l expr :=
  lazymatch expr with
  | (match ?o with inl _ => _ | inr _ => _ end) =>
    lazymatch eval pattern o in expr with
    | ?F _ => eval cbv beta iota in (fun a => F (inl a))
    end
  end.

Ltac sum_match_fun_r expr :=
  lazymatch expr with
  | (match ?o with inl _ => _ | inr _ => _ end) =>
    lazymatch eval pattern o in expr with
    | ?F _ => eval cbv beta iota in (fun a => F (inr a))
    end
  end.

Ltac to_dummy' i p :=
  lazymatch p with
  | pipe ?c ?f =>
    let init := get_init c in
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy' (S i) x in
    lazymatch d with
    | context [dummy _ ?T i] =>
      lazymatch (eval pattern (dummy _ T i) in d) with
      | ?g _ =>
        constr:((pipe, init, g))
      end
    end
  | @Eff ?eff ?args ?rets ?C ?e ?a ?f =>
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy' (S i) x in
    lazymatch type of f with
    | ?T -> _ =>
      lazymatch (eval pattern (dummy _ T i) in d) with
      | ?g _ =>
        constr:((@Eff eff args rets C e a, g))
      end
    end
  | @proc_coro ?A ?B ?C ?D ?eff ?args ?rets ?state ?step ?c ?z ?f =>
    let x := (eval cbv beta in (f (dummy _ _ i) (dummy _ _ (S i)))) in
    lazymatch f with
    | (*context [proc_coro]*) _  =>
      let d := to_dummy' (S (S i)) x in
      lazymatch type of f with
      | _ -> ?T -> _ =>
        lazymatch (eval pattern (dummy _ A i), (dummy _ T (S i)) in d) with
        | ?g _ _ =>
          constr:((@seq_abs A B eff args rets D state step z (coro_type step) c, g))
        end
      end(*
    | _ =>
      constr:((@seq_abs A B eff args rets D state step z (coro_type step) c, f))
*)
    end
  | @bind ?T ?T' ?eff ?args ?rets ?p ?f =>
    let x :=  (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy' (S i) x in
    lazymatch (eval pattern (dummy _ T i) in d) with
    | ?g _ =>
      constr:((@bind T T' eff args rets p, g))
    end
  | (match ?o with inl _ => _ | inr _ => _ end) =>
    let fl := sum_match_fun_l p in
    let fr := sum_match_fun_r p in
    let ty := type of fl in
    lazymatch ty with
    | ?A -> _ =>
      let ty' := type of fr in
      lazymatch ty' with
      | ?B -> _ =>
        let xl := (eval cbv beta in (fl (dummy _ _ i))) in
        let xr := (eval cbv beta in (fr (dummy _ _ i))) in
        let dl := to_dummy' (S i) xl in
        let dr := to_dummy' (S i) xr in
        lazymatch (eval pattern (dummy _ A i) in dl) with
        | ?gl _ =>
          lazymatch (eval pattern (dummy _ B i) in dr) with
          | ?gr _ => constr:((@sum_merge A B, gl, gr, o))
          end
        end
      end
    end
  | (match ?o with Some _ => _ | None => ?f0 end) =>
    let f := opt_match_fun p in
    let ty := type of o in
    lazymatch ty with
    | option ?A =>
      let B := type of p in
      let x := (eval cbv beta in (f (dummy _ _ i))) in
      let d := to_dummy' (S i) x in
      let d0 := to_dummy' i f0 in
      lazymatch (eval pattern (dummy _ A i) in d) with
      | ?g _ =>
        constr:((@option_branch A B, g, d0, o))
      end
    | _ =>
      lazymatch (eval simpl in ty) with
      | option ?A =>
        let B := type of p in
        let x := (eval cbv beta in (f (dummy _ _ i))) in
        let d := to_dummy' (S i) x in
        let d0 := to_dummy' i f0 in
        lazymatch (eval pattern (dummy _ A i) in d) with
        | ?g _ =>
          constr:((@option_branch A B, g, d0, o))
        end
      end
    end
  | (match ?o with (a,b) => _ end) =>
    lazymatch (eval pattern o in p) with
    | ?F _ =>
      let f := (eval cbv beta iota in (fun a b => F (a,b))) in
      let x := (eval cbv beta in (f (dummy _ _ i) (dummy _ _ (S i)))) in
      let d := to_dummy' (S (S i)) x in
      lazymatch type of o with
      | ?A * ?B =>
        lazymatch (eval pattern (dummy _ A i), (dummy _ B (S i)) in d) with
        | ?g _ _ => constr:((@prod_curry A B, g, o))
        end
      end
    end
  | @nat_rect_nondep ?A ?f ?f0 ?n ?a =>
    let x := (eval cbv beta in (f0 (dummy _ _ i) (dummy _ _ (S i)) (dummy _ _ (S (S i))))) in
    let y := (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy' (S i) y in
    let d0 := to_dummy' (S (S (S i))) x in
(*    let T := type of a in*)
    lazymatch A with
      ?T -> _ =>
      lazymatch (eval pattern (dummy _ nat i), (dummy _ A (S i)), (dummy _ T (S (S i))) in d0) with
      | ?g0 _ _ _ =>
        lazymatch (eval pattern (dummy _ T i) in d) with
        | ?g _ =>
          constr:((@nat_rect_nondep A, g, g0, n, a))
        end
      end
    end
  | @list_rec_nondep ?A ?B ?f ?f0 ?l ?a =>
    let x := (eval cbv beta in (f0 (dummy _ _ i) (dummy _ _ (S i)) (dummy _ _ (S (S i))) (dummy _ _ (S (S (S i)))))) in
    let y := (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy' (S i) y in
    let d0 := to_dummy' (S (S (S (S i)))) x in
    let T := type of a in
    lazymatch (eval pattern (dummy _ A i), (dummy _ (list A) (S i)), (dummy _ B (S (S i))) , (dummy _ T (S (S (S i)))) in d0) with
    | ?g0 _ _ _ _ =>
      lazymatch (eval pattern (dummy _ T i) in d) with
      | ?g _ =>
        constr:((@list_rec_nondep A, B, g, g0, l, a))
      end
    end
  | _ => p
  end.

Ltac reconstruct' tree i :=
  lazymatch tree with
  | (pipe, ?init, ?f) =>
    let x := (eval cbv beta in (f init)) in
    reconstruct' x i
  | (Eff ?e ?a, ?p) =>
    let x := (eval cbv beta in (p (dummy _ _ i))) in
    let p' := reconstruct' x (S i) in
    lazymatch type of p with
    | ?ty -> _ =>
      let ty' := (eval cbv beta in ty) in
      lazymatch (eval pattern (dummy _ ty' i) in p') with
      | ?p'' _ =>
        constr:(Eff e a p'')
      end
    end
  | (@seq_abs ?A ?B ?eff ?args ?rets ?C _ ?step ?z ?state ?st, ?p) =>
    let x := (eval cbv beta in (p (dummy _ _ i) (dummy _ _ (S i)))) in
    let p' := reconstruct' x (S (S i)) in
    lazymatch (eval pattern (dummy _ A i), (dummy _ state (S i)) in p') with
    | ?p'' _ _ =>
      constr:(@step_state A B _ _ eff args rets _ step st z p'')
    end
  | (@bind ?T ?T' ?eff ?args ?rets ?p, ?g) =>
    let x := (eval cbv beta in (g (dummy _ _ i))) in
    let q := reconstruct' x (S i) in
    lazymatch (eval pattern (dummy _ T i) in q) with
    | ?g' _ =>
      constr:(@bind T T' eff args rets p g')
    end
  | (@sum_merge ?A ?B, ?fl, ?fr, ?o) =>
    let xl := (eval cbv beta in (fl (dummy _ _ i))) in
    let ql := reconstruct' xl (S i) in
    let xr := (eval cbv beta in (fr (dummy _ _ i))) in
    let qr := reconstruct' xr (S i) in
    lazymatch (eval pattern (dummy _ A i) in ql) with
    | ?pl' _ =>
      lazymatch (eval pattern (dummy _ B i) in qr) with
      | ?pr' _ => constr:(@sum_merge A B _ pl' pr' o)
      end
    end
  | (@option_branch ?A ?B, ?f, ?f0, ?o) =>
    let q := reconstruct' f0 i in
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let p' := reconstruct' x (S i) in
    lazymatch (eval pattern (dummy _ A i) in p') with
    | ?p'' _ =>
      constr:(@option_branch A B p'' q o)
    end
  | (@prod_curry ?A ?B, ?f, ?o) =>
    let x := (eval cbv beta in (f (dummy _ _ i) (dummy _ _ (S i)))) in
    let q := reconstruct' x (S (S i)) in
    lazymatch (eval pattern (dummy _ A i), (dummy _ B (S i)) in q) with
    | ?p' _ _ =>
      constr:(let (_a,_b) := o in p' _a _b)
    end
  | (@nat_rect_nondep ?A, ?f, ?f0, ?n, ?a) =>
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let y := (eval cbv beta in (f0 (dummy _ _ i) (dummy _ _ (S i)) (dummy _ _ (S (S i))))) in
    let f' := reconstruct' x (S i) in
    let f0' := reconstruct' y (S (S (S i))) in
    (*    let ty := type of a in*)
    lazymatch A with
      ?ty -> _ =>
      lazymatch (eval pattern (dummy _ ty i) in f') with
      | ?f'' _ =>
        lazymatch (eval pattern (dummy _ nat i), (dummy _ A (S i)), (dummy _ ty (S (S i))) in f0') with
        | ?f0'' _ _ _ =>
          constr:(@nat_rect_nondep A f'' f0'' n a)
        end
      end
    end
  | (@list_rec_nondep ?A, ?B, ?f, ?f0, ?l, ?a) =>
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let y := (eval cbv beta in (f0 (dummy _ _ i) (dummy _ _ (S i)) (dummy _ _ (S (S i))) (dummy _ _ (S (S (S i)))))) in
    let f' := reconstruct' x (S i) in
    let f0' := reconstruct' y (S (S (S (S i)))) in
    let ty := type of a in
    lazymatch (eval pattern (dummy _ ty i) in f') with
    | ?f'' _ =>
      lazymatch (eval pattern (dummy _ A i), (dummy _ (list A) (S i)), (dummy _ B (S (S i))), (dummy _ ty (S (S (S i)))) in f0') with
      | ?f0'' _ _ _ _ =>
        constr:(@list_rec_nondep A B f'' f0'' l a)
      end
    end
  | _ => tree
  end.

Ltac coro_to_state' p :=
  let x := to_dummy' 0 p in
  lazymatch x with
  | context [@coro_type ?A ?B ?C ?state ?step] =>
    lazymatch (eval pattern (@coro_type A B C state step) in x) with
    | ?F _ =>
      let y := (eval cbv beta in (F state)) in
      reconstruct' y 0
    end
  end.

Ltac mid_eq_core' :=
  discriminate
  || dest_match
  || proc_step
  || apply eq_refl
  || (progress (repeat match goal with
                       | H : _ |- _ => apply H
                       end);
      ((simpl in *; congruence) || solve [eauto with foldable equivc] || solve [simpl; eauto]))
  || generalize_and_ind
  || lazymatch goal with
       |- Eff ?e ?a ?f = Eff _ _ ?f0 =>
       apply (@f_equal _ _ (fun x => Eff e a x) f f0);
       let H := fresh in
       extensionality H
     | |- (_ <<- _ ; _) = (_ <<- _ ; _ ) =>
       f_equal;
       let H := fresh in
       extensionality H
     end
  || eauto with foldable equivc.

Definition main_loop_derive  :
  { state & { step & forall fuel fuel' certs keys,
                { init | @equiv _ _ _ _ state step init (main_loop fuel fuel' certs keys) } } }.
Proof.
  do 3 eexists.
  Set Ltac Profiling.
  
  lazymatch goal with
    |- equiv _ ?init ?x =>
    let u := open_constr:(inl (tt,fuel,fuel',certs,keys)) in
    unify init u;
    let H := fresh in
    assert (x = ltac:(let x' := eval red in x in
                          let x'' := coro_to_state' x' in exact x''))
  end.
  unfold main_loop,pipe,sum_merge.
  repeat mid_eq_core'.
  rewrite H;
    clear H;
    unfold step_state.
    repeat eexists;
    [ dest_step
    | unfold option_branch, sum_merge;
      derive_core open_constr:(fun a => inr a) (tt,fuel,fuel',certs,keys) ].
  all:lazymatch goal with
    |- equiv' ?step _ _ (Return ?r) _ =>
    (let ptr := next_ptr open_constr:(fun _x => _x) in
     eapply (Equiv'Return step _ (ptr r));
     simpl;
     split;
     lazymatch goal with
       |- _ ?x = _ =>
       pattern_rhs x;
       eapply eq_refl
     | _ => eapply eq_refl
     end)
    || (eapply (Equiv'Return step);
        simpl;
        split;
        lazymatch goal with
          |- _ ?x = _ =>
          pattern_rhs x;
          eapply eq_refl
        | _ => eapply eq_refl
        end)
  end.

  
  (*derive (tt,fuel,fuel',certs,keys).*)
  Grab Existential Variables.
  all: exact inhabitant.
Time Defined.


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
Extract Inductive Header => "I.Header" ["I.Header"].
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
Extract Constant decodeHeader => "\bs  -> case I.decodeHeader bs of Prelude.Right a -> GHC.Base.Just a ; _ -> GHC.Base.Nothing".
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

Extract Constant extension_KeyShare =>
"(\exts -> case Helper.extensionLookup I.extensionID_KeyShare exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.KeyShareClientHello kses) -> GHC.Base.return kses})".
Extract Constant serverGroups => "Helper.serverGroups".
Extract Constant changeCipherSpec => "\p -> case p of { I.ChangeCipherSpec13 -> GHC.Base.Just (); _ -> GHC.Base.Nothing }".
Extract Constant extension_SignatureAlgorithms =>
"(\exts -> case Helper.extensionLookup I.extensionID_SignatureAlgorithms exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.SignatureAlgorithms sas) -> GHC.Base.Just sas; _ -> GHC.Base.Nothing })".
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
Extract Constant life => "172800".
Extract Constant Word64gt => "(Prelude.>)".
Extract Constant Word32le => "(Prelude.<=)".
Extract Constant w64_2000 => "2000".
Extract Constant extension_ServerName => "\exts -> Helper.extensionLookup I.extensionID_ServerName exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello".
Extract Constant Word64minus => "(Prelude.-)".
Extract Constant w32to64 => "Prelude.fromIntegral".
Extract Constant Word32minus => "(Prelude.-)".
Extract Constant maxCiphertextSize => "16384".
Extract Constant bytes2w32 => "B.foldl' (\x y -> x Prelude.* 256 Prelude.+ Prelude.fromIntegral y) 0".
Extract Constant Version_beq => "(Prelude.==)".
Extract Constant Word64plus => "(Prelude.+)".
Extract Constant extension_SupportedVersionsCH => "\exts -> case Helper.extensionLookup I.extensionID_SupportedVersions exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of {GHC.Base.Just (I.SupportedVersionsClientHello vers) -> GHC.Base.Just vers; _ -> GHC.Base.Nothing }".
Extract Constant Word64max => "Prelude.max".

Require Extraction.
Extraction Language Haskell.

Extraction "TLS.hs" main_loop_step.
