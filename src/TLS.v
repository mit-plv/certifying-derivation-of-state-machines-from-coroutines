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

Parameter extension_KeyShare : list ExtensionRaw -> option (list KeyShare).
Parameter extension_NegotiatedGroups : list ExtensionRaw -> list Group.
Parameter Word32 : Set.
Parameter PublicKey PrivateKey : Set.
Parameter GroupPublic GroupKey : Set.
Parameter Hash Cipher HashAndSignatureAlgorithm : Set.
Parameter KeyUpdate : Set.
Parameter Certificate CertificateChain : Set.
Parameter Signature : Set.

(*
Definition CHandshake :=
  ClientHelloMsg + ByteString.
 *)

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
Inductive CPacket :=
| PHandshake : list CHandshake -> CPacket
| PChangeCipherSpec : CPacket
| PAppData13 : ByteString -> CPacket.

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
  | PAppData13 dat => Some dat
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

Inductive eff_tls := recvData | getRandomBytes | sendPacket | groupGetPubShared | makeCertVerify.

Parameter Packet13 Handshake13 : Set.

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
Parameter handshake13 : list Handshake13 -> Packet13.
Parameter serverHello13 : ByteString -> Session -> CipherID -> list ExtensionRaw -> Handshake13.
(*Parameter changeCipherSpec : Packet13.*)
Parameter extension_SignatureAlgorithms : list ExtensionRaw -> list (HashAndSignatureAlgorithm).


Parameter getCertificates : CertificateChain -> list Certificate.
Parameter defaultCertChain : PublicKey -> CertificateChain.
Parameter certificate13 : ByteString -> CertificateChain -> list (list ExtensionRaw) -> Handshake13.
Parameter empty : ByteString.
Parameter ciphersuite_default : list Cipher.
Parameter hashWith : Hash -> list ByteString -> ByteString.
Parameter encryptedExtensions13 : list ExtensionRaw -> Handshake13.
Parameter sniExt : ExtensionRaw.
Parameter appData13 : ByteString -> Packet13.

Parameter encodeEncryptedExt : list ExtensionRaw -> ByteString.
Parameter CryptoError : Set.
Parameter encodeGroupPublic : GroupPublic -> ByteString.
Parameter decodeGroupPublic : Group -> ByteString -> option GroupPublic.
Parameter ba_convert : GroupKey -> ByteString.
Parameter hashDigestSize : Hash -> nat.
Parameter Word8 : Set.
Parameter b_replicate : nat -> Word8 -> ByteString.
Parameter w0 : Word8.
Parameter hkdfExtract : Hash -> ByteString -> ByteString -> ByteString.
Parameter hkdfExpandLabel : Hash -> ByteString -> ByteString -> ByteString -> nat -> ByteString.
Parameter s2b : String.string -> ByteString.
Parameter finished13 : ByteString -> Handshake13.
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

Fixpoint decideCredInfo
         (priv : PrivateKey)
         (certs : list Certificate)
         (hashSigs : list (HashAndSignatureAlgorithm)) :=
  match hashSigs with
  | [] => None
  | hashSig::rest =>
    match decideCredInfo' priv hashSig certs with
    | None => decideCredInfo priv certs rest
    | Some res => Some res
    end
  end.

(*
Instance ByteString_inhabitant : Inhabit ByteString :=
  { inhabitant := empty }.

Parameter hashdummy : Hash.
Instance Hash_inhabitant : Inhabit Hash :=
  { inhabitant := hashdummy }.

Parameter session : Session.
Instance clientHelloMSg_inhabitant : Inhabit ClientHelloMsg :=
  { inhabitant := {| chSession := session; chExtension := []; chCiphers := [] |} }.

*)
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

Parameter TicketInfo : Set.
Parameter CompressionID : Set.
Inductive SessionFlag := SessionEMS : SessionFlag.

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

Parameter dummyCompressionID : CompressionID.

Definition args_tls' :=
  String.string * SessionData + String.string + CPacket * option (Hash * Cipher * ByteString * nat) + nat + unit + GroupPublic + PublicKey * PrivateKey * HashAndSignatureAlgorithm * ByteString + CPacket * option (Hash * Cipher * ByteString) + (unit + unit + unit + unit) * option (Hash * Cipher * ByteString).

Definition rets_tls' :=
   option SessionData + option (GroupPublic * GroupKey) + CHandshake + ByteString + unit + ByteString * ClientHelloMsg.

Notation "r <- 'yield' 'SetPSK' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inl (inl (inl a))))))))
       (fun r' => ((fun _ => Return tt) ||| (fun r => p) ||| (fun _ => Return tt)) r'))
    (at level 100, right associativity).
Notation "r <- 'yield' 'SessionResume' $ a & o ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inl (inl (inr a))))))))
       (fun r' => ((fun r => p) ||| (fun _ => Return o) ||| (fun _ => Return o) ||| (fun _ => Return o) ||| (fun _ => Return o) ||| (fun _ => Return o)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvClientHello' $ a ; p" :=
  (Eff yield (inr (inr tt, a))
       (fun r' => ((fun _ => Return tt) ||| (fun r => p)) r'))
       (at level 100, right associativity).

Notation "r <- 'yield' 'RecvData' $ a & o ; p" :=
  (Eff yield (inl (inl (inl (inl (inr a)))))
       (fun r' => ((fun _ => Return o) ||| (fun r => p) ||| (fun _ => Return o) ||| (fun _ => Return o)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvFinished' $ a ; p" :=
  (Eff yield (inr (inl (inl (inr tt)), a))
       (fun r' => ((fun _ => Return tt) ||| (fun r => p) ||| (fun _ => Return tt) ||| (fun _ => Return tt)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvCCS' $ a ; p" :=
  (Eff yield (inr (inl (inr tt), a))
       (fun r' => ((fun _ => Return tt) ||| (fun r => p) |||(fun _ => Return tt)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvAppData' $ a ; p" :=
  (Eff yield (inr (inl (inl (inl tt)), a))
       (fun r' => ((fun _ => Return tt) ||| (fun r => p) ||| (fun _ => Return tt) ||| (fun _ => Return tt)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'GetRandomBytes' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inr a))))))
       (fun r' => ((fun _ => Return tt) ||| (fun r => p) ||| (fun _ => Return tt) ||| (fun _ => Return tt)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'SendPacket' $ a & o ; p" :=
  (Eff yield (inl (inr a))
       (fun r' => ((fun _ => Return o) ||| (fun r => p) ||| (fun _ => Return o)||| (fun _ => Return o)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'GroupGetPubShared' $ a ; p" :=
  (Eff yield (inl (inl (inl (inr a))))
       (fun r' => ((fun _ => Return tt) ||| (fun r => p) ||| (fun _ => Return tt) ||| (fun _ => Return tt) ||| (fun _ => Return tt) ||| (fun _ => Return tt)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'MakeCertVerify' $ a & o ; p" :=
  (Eff yield (inl (inl (inr a)))
       (fun r':rets_tls' => ((fun _ => Return o) ||| (fun r => p) ||| (fun _ => Return o) ||| (fun _ => Return o) ||| (fun _ => Return o)) r'))
    (at level 100, right associativity).

Instance sigT_rets_inhabit : Inhabit rets_tls' :=
  { inhabitant := inl (inr tt) }.

Instance sigT_argss_inhabit : Inhabit args_tls' :=
  { inhabitant := (inl (inl (inl (inl (inr tt))))) }.

Parameter ProtocolType : Set.
Inductive Header := header : ProtocolType -> Version -> nat -> Header.

Definition hdReadLen hd :=
  match hd with
  | header _ _ n => n
  end.

Parameter decodeHeader : ByteString -> Header.
Parameter decodeRecord : Header -> option (Hash * Cipher * ByteString * nat) -> ByteString -> option CPacket.
Parameter Bsplit :  nat -> ByteString -> ByteString * ByteString.

Notation "x <~ 'ifSome' o 'else' q ; p" :=
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

Definition checkSessionEquality usedCipher ciphers (*alpn*) sdata :=
  let isSameCipher := CipherID_beq (sessionCipher sdata) (cipherID usedCipher) in
  let isSameKDF :=
      match find (fun c => CipherID_beq (cipherID c) (sessionCipher sdata)) ciphers with
      | None => false
      | Some c => Hash_beq (cipherHash c) (cipherHash usedCipher)
      end
  in
(*  let isSameALPN := option_beq ByteString_beq (sessionALPN sdata) alpn in*)
  (isSameKDF, isSameCipher(* && isSameALPN*)).

Inductive PskIdentity := Build_PskIdentity : ByteString -> Word32 -> PskIdentity.

Inductive PreSharedKey :=
| PreSharedKeyClientHello : list PskIdentity -> list ByteString -> PreSharedKey
| PreSharedKeyServerHello : nat -> PreSharedKey.

Parameter extension_PreSharedKey : list ExtensionRaw -> option PreSharedKey.

Definition extension_PreSharedKeyCH exts :=
  match extension_PreSharedKey exts with
  | Some (PreSharedKeyClientHello (Build_PskIdentity sessionID obfAge :: _) bnds) =>
    Some (sessionID, obfAge, bnds)
  | _ => None
  end.

Definition sumnat l :=
  fold_left Nat.add l 0.
Parameter b2s : ByteString -> String.string.

Definition choosePSK exts dhModes usedCipher ciphers (*alpn*) zero : t (const_yield args_tls') (const_yield rets_tls') (option (ByteString * option _ * bool)) :=
  match extension_PreSharedKeyCH exts with
  | Some (sessionID, obfAge, bnds) =>
    bnd <~ ifSome hd_error bnds else Return None;
    if inb PskKexMode_beq PSK_DHE_KE dhModes then
      let len := (sumnat (map (fun x => Blength x + 1) bnds) + 2)%nat in
      osdata <- yield SessionResume $ (b2s sessionID) & None;
      sdata <~ ifSome osdata else Return (Some (zero, None, false));
      tinfo <~ ifSome sessionTicketInfo sdata else Return (Some (zero, None, false));
      let psk := sessionSecret sdata in
(*      isFresh <<- checkFreshness tinfo obfAge;*)
      let (isPSKValid, is0RTTValid) := checkSessionEquality usedCipher ciphers (*alpn*) sdata in
      if isPSKValid (* && isFresh *) then
        Return (Some (psk, Some (bnd, 0, len), is0RTTValid))
      else Return (Some (zero, None, false))
    else Return (Some (zero, None, false))
  | _ => Return (Some (zero, None, false))
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
  | None => []
  | Some (binder, n, tlen) =>
    let binder' := makePSKBinder chEncoded earlySecret usedHash tlen hsize in
    if ByteString_beq binder' binder then
      let selectedIdentity := extensionEncode_PreSharedKey (PreSharedKeyServerHello n) in
      [ExtensionRaw_PreSharedKey selectedIdentity]
    else []
  end.
 
Fixpoint chooseServerName ns :=
  match ns with
  | [] => None
  | name::rest =>
    match name with
    | ServerNameHostName hostName => Some hostName
    | _ => chooseServerName rest
    end
  end.

Parameter encodeHandshake13 : CHandshake -> ByteString.
Parameter extension_PskKeyModes : list ExtensionRaw -> option (list PskKexMode).
Parameter nat2Word32 : nat -> Word32.
Parameter lifetime addAge : Word32.


Parameter packet2tinfo : CPacket -> option TicketInfo.

Definition doHandshake (fuel:nat) (cch: CertificateChain)(pr: PrivateKey)(_: rets_tls')
  : t (const_yield args_tls') (const_yield rets_tls') unit := Eval unfold option_branch in
  let certs := getCertificates cch in
  d' <- yield RecvClientHello $ None;
  let (chEncoded, se) := (d' : ByteString * ClientHelloMsg) in
  let sess := chSess se in
  let chExts := chExt se in
  let cipherIDs := chCipherIDs se in
  cipher <~ ifSome chooseCipher cipherIDs serverCiphers else Return tt;
  keyShares <~ ifSome extension_KeyShare chExts else Return tt;
  keyShare <~ ifSome findKeyShare keyShares serverGroups else Return tt;
  cpub <~ ifSome decodeGroupPublic (ksGroup keyShare) (ksData keyShare) else Return tt;
  mecdhePair <- yield GroupGetPubShared $ cpub;
  ecdhePair <~ ifSome mecdhePair else Return tt;
  let wspub := encodeGroupPublic (fst ecdhePair) in
  let ecdhe := ba_convert (snd ecdhePair) in
  let serverKeyShare := {| ksGroup := ksGroup keyShare; ksData := wspub |} in
(*  let serverName :=
      match extension_ServerName chExts with
      | Some (Build_ServerName ns) => chooseServerName ns
      | None => None
      end
  in
  protos <~ ifSome extension_ApplicationLayerProtocolNegotiation chExts else Return tt;
*)
  
  (* sendServerHello *)
  let ks := extensionEncode_KeyShare serverKeyShare in
  let selectedVersion := extensionEncode_SupportedVersions TLS13 in
  let usedHash := cipherHash cipher in
  let hsize := hashDigestSize usedHash in
  let zero := b_replicate hsize w0 in
  dhModes <~ ifSome extension_PskKeyModes chExts else Return tt;
  p' <<- choosePSK chExts dhModes cipher serverCiphers (*alpn*) zero;
  p <~ ifSome p' else Return tt;
  let (pb, is0RTTValid) := p : ByteString * option (ByteString * nat * nat) * bool in
  let (psk, binderInfo) := pb in
  let earlySecret := hkdfExtract usedHash zero psk in
  let extensions := checkBinder chEncoded usedHash earlySecret binderInfo hsize in
  let extensions' :=
      extensionRaw_KeyShare ks :: extensionRaw_SupportedVersions selectedVersion  :: extensions
  in
  srand <- yield GetRandomBytes $ 32;
  shEncoded <- yield SendPacket $
            (PHandshake [HServerHello (SR srand) sess (cipherID cipher) extensions'], None) & tt;

  (* calculate handshake secrets *)
  let hCh := hashWith usedHash [chEncoded; shEncoded] in
  let clientEarlySecret := hkdfExpandLabel usedHash earlySecret (s2b "c e traffic") hCh hsize in
  
  let handshakeSecret := hkdfExtract usedHash (hkdfExpandLabel usedHash earlySecret (s2b "derived") (hashWith usedHash [s2b ""]) hsize) ecdhe in
  let clientHandshakeSecret := hkdfExpandLabel usedHash handshakeSecret (s2b "c hs traffic") hCh hsize in
  let serverHandshakeSecret := hkdfExpandLabel usedHash handshakeSecret (s2b "s hs traffic") hCh hsize in

  ccsEncoded <- yield SendPacket $ (PChangeCipherSpec, None) & tt;
  extEncoded <- yield SendPacket $
             (PHandshake [HEncryptedExtensions []], Some (usedHash, cipher, serverHandshakeSecret)) & tt;
  let sendCertAndVerify :=
      let transcript := [chEncoded; shEncoded; extEncoded] in
      match binderInfo with
      | Some _ => Return (Some transcript)
      | None =>
        let hashSigs := extension_SignatureAlgorithms chExts in
        pubhs <~ ifSome decideCredInfo pr certs hashSigs else Return None;
        let (pub,hashSig) := pubhs : PublicKey * HashAndSignatureAlgorithm in
        certEncoded <- yield SendPacket $
                    (PHandshake [HCertificate empty cch [[]]], Some (usedHash, cipher, serverHandshakeSecret)) & None;
        let hashed := hashWith (cipherHash cipher) ([chEncoded;shEncoded;extEncoded;certEncoded]) in
        cv <- yield MakeCertVerify $ (pub,pr,hashSig,hashed) & None;
        cvEncoded <- yield SendPacket $
                  (PHandshake [cv], Some (usedHash, cipher, serverHandshakeSecret)) & None;
        Return (Some (transcript ++ [certEncoded; cvEncoded])%list)
      end
  in
  otranscript <<- sendCertAndVerify;
  transcript <~ ifSome otranscript else Return tt;
  
  let hashed' := hashWith (cipherHash cipher) transcript in
  finEncoded <- yield SendPacket $
             (PHandshake [HFinished (makeVerifyData usedHash serverHandshakeSecret hashed')],
              Some (usedHash, cipher, serverHandshakeSecret)) & tt;
  let hashed'' := hashWith (cipherHash cipher) (transcript ++ [finEncoded]) in
  let applicationSecret := hkdfExtract usedHash (hkdfExpandLabel usedHash handshakeSecret (s2b "derived") (hashWith usedHash [s2b ""]) hsize) zero in
  let clientApplicationSecret := hkdfExpandLabel usedHash applicationSecret (s2b "c ap traffic") hashed'' hsize in
  let serverApplicationSecret := hkdfExpandLabel usedHash applicationSecret (s2b "s ap traffic") hashed'' hsize in

  _ <- yield RecvCCS $ None;
  fin <- yield RecvFinished $ (Some (usedHash, cipher, clientHandshakeSecret));

  (* calculate application secrets *)
  let hashed''' := hashWith (cipherHash cipher) (transcript ++ [finEncoded; encodeHandshake13 (HFinished fin)]) in
  let resumptionMasterSecret := hkdfExpandLabel usedHash applicationSecret (s2b "res master") hashed''' hsize in
  if ByteString_beq fin (makeVerifyData usedHash clientHandshakeSecret hashed'') then
    let pac := PHandshake [HNewSessionTicket lifetime addAge (s2b "0") (s2b "TestSession") []] in
    _ <- yield SetPSK $ ("TestSession",
                         {| sessionVersion := TLS13;
                            sessionCipher := cipherID cipher;
                            sessionGroup := None;
                            sessionTicketInfo := packet2tinfo pac;
                            sessionCompression := dummyCompressionID;
                            sessionClientSNI := None;
                            sessionSecret := hkdfExpandLabel usedHash resumptionMasterSecret (s2b "resumption") (s2b "0") hsize;
                            sessionALPN := None;
                            sessionMaxEarlyDataSize := 5;
                            sessionFlags := []
                        |});
    _ <- yield SendPacket $ (pac, Some (usedHash, cipher, serverApplicationSecret)) & tt;
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
  else Return tt
.

Opaque replicate.

Definition doHandshake_derive :
  { state & { step &
              forall fuel certs priv,
                { init | @equiv_coro _ _ _ _ _ state step init (doHandshake fuel certs priv) }}}.
Proof.
  do 3 eexists.
  unfold doHandshake.
  unfold choosePSK, option_branch.
  derive_coro (tt,fuel,certs,priv).
  Grab Existential Variables.
  all: exact inhabitant.
Time Defined.

Definition doHandshake_step := projT1 (projT2 doHandshake_derive).

Definition doHandshake_equiv fuel certs keys :
  equiv_coro doHandshake_step (inl (tt,fuel,certs,keys)) (doHandshake fuel certs keys) :=
  proj2_sig (projT2 (projT2 doHandshake_derive) fuel certs keys).

Hint Resolve doHandshake_equiv : equivc.

Notation "r <- 'yield' 'SendData' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inl (inr a)))))))
       (fun r => p))
    (at level 100, right associativity).

Definition parse header bs (s:unit+unit+unit+unit) o : t (const_yield args_tls') (const_yield rets_tls') (option (String.string + rets_tls')) :=
  match decodeRecord header o bs with
  | None => Return (Some (inl "decode failed"))
  | Some r => 
    match s with
    | inr _ =>
      match clientHello r with
      | None => Return (Some (inl "cliehthello not match"))
      | Some c => Return (Some (inr (inr (bs,c))))
      end
    | inl (inr _) =>
      match changeCipherSpec r with
      | None => Return (Some (inl "changecipherspec not match"))
      | Some _ => Return (Some (inr (inl (inr tt))))
      end
    | inl (inl (inr _)) =>
      match handshake r with
      | None => Return (Some (inl "handshake not match"))
      | Some h =>
        match finished h with
        | None => Return (Some (inl "finished not match"))
        | Some f => Return (Some (inr (inl (inl (inr f)))))
        end
      end
    | inl (inl (inl _)) =>
      match appData r with
      | None => Return (Some (inl "appdata not match"))
      | Some a => Return (Some (inr (inl (inl (inr a)))))
      end
    end
  end.

Definition seqNum (tbl : list (ByteString * nat))(key : ByteString) :=
  (fix aux pre tbl :=
     match tbl with
     | [] => ((key,1)::pre, 0)
     | (k,n)::rest =>
       if ByteString_beq k key then
         ((k,S n)::pre ++ tbl, n)%list
       else aux ((k,n)::pre) rest
     end) [] tbl.

(*
Parameter encodePacket : CPacket -> option (Hash * Cipher * ByteString * nat) -> ByteString.
*)

Definition readWrite fuel certs keys(_: rets_tls') : t (const_yield _) (const_yield rets_tls') (option String.string) := Eval unfold parse in
  pipe (doHandshake fuel certs keys) (fun coro : coro_type doHandshake_step =>
  nat_rect_nondep
    (fun _ => Return None)
    (fun _ rec (ctx: list (ByteString * nat) * option ((unit+unit+unit+unit)*option (Hash*Cipher*ByteString)) * ByteString * rets_tls' * coro_type doHandshake_step) =>
       match ctx with
       | (tbl,s,bs,a,c) =>
       match s with
       | None =>
         r <- resume c $ a;
         match r with
         | inr eo =>
           _ <- yield (inl (inl (inl (inl (inl (inr 1))))));
(*           _ <- yield GetRandomBytes $ 1; *) (* needed for compiler limitation *)
             rec (tbl, Some eo, mconcat [bs], a, c)
         | inl (inr (pkt,o)) =>
           match o with
           | None =>
             a' <- yield SendData $ (pkt, None);
               rec (tbl, None, bs, a', c)
           | Some sec =>
             let (tbl', num) := seqNum tbl (snd sec) in
             a' <- yield SendData $ (pkt, (Some (sec, num)));
               rec (tbl', None, bs, a', c)
           end
         | _ =>
           a' <- yield r;
             rec (tbl, None, bs, a', c)
         end
       | Some o =>
         if Nat.ltb (Blength bs) 5 then
           bs' <- yield RecvData $ tt & Some "fail";
             rec (tbl, Some o, mconcat [bs; bs'], a, c)
         else
           let p := Bsplit 5 bs in
           let header := decodeHeader (fst p) in
           if Nat.ltb (Blength (snd p)) (hdReadLen header) then
             bs' <- yield RecvData $ tt & Some "fail";
             rec (tbl, Some o, mconcat [bs; bs'], a, c)
           else
             let p' := Bsplit (hdReadLen header) (snd p) in
             let o' :=
                 match snd o with
                 | None => (tbl, None)
                 | Some sec =>
                   let p := seqNum tbl (snd sec) in
                   (fst p, Some (sec, snd p))
                 end
             in
             a' <<- parse header (fst p') (fst o) (snd o');
               match a' with
               | Some (inr a'') =>
                 _ <- yield (inl (inl (inl (inl (inl (inr 1))))));
                 rec (fst o', None, snd p', a'', c)
               | Some (inl err) => Return (Some err)
               | None => Return None
                 end
     end
     end)
    fuel ([], None,empty, inl (inr tt), coro)).

Inductive GenForall2_prod_r (A A1 A2 : Set)(R : A1 -> A2 -> Prop) : A * A1 -> A * A2 -> Prop :=
  GenForall2_prod_r_rule : forall a x1 x2, R x1 x2 -> GenForall2_prod_r A A1 A2 R (a,x1) (a,x2).

Program Instance prod_r_HasGenForall2 (A:Set) : HasGenForall2 (prod A) :=
  { GenForall2 := GenForall2_prod_r A }.

Program Instance id_HasGenForall2 : HasGenForall2 (fun A:Set => A) :=
  { GenForall2 := fun A1 A2 R => R }.

Instance ByteString_inhabitant : Inhabit ByteString :=
  { inhabitant := empty }.

Definition readWrite_derive :
  { state & { step &
              forall fuel certs priv,
                { init | @equiv_coro _ _ _ _ _ state step init (readWrite fuel certs priv) } } }.
Proof.
  do 3 eexists.

  unshelve derive (tt,fuel,certs,priv); exact inhabitant.
Time Defined.

Inductive eff_conn := newAccept | perform | receive.


Definition args_conn (e : eff_conn) :=
  match e with
  | newAccept => unit
  | perform => string * args_tls'
  | receive => unit
  end.

Definition rets_conn (e : eff_conn) :=
  match e with
  | newAccept => option string
  | perform => unit
  | receive => option (string * rets_tls')
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

Definition isSetPSK (x : args_tls') :=
  match x with
  | inl (inl (inl (inl (inl (inl (inl (inl x))))))) => Some x
  | _ => None
  end.

Definition isSessionResume (x : args_tls') :=
  match x with
  | inl (inl (inl (inl (inl (inl (inl (inr x))))))) => Some x
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

Definition main_loop fuel fuel' certs keys :=
  nat_rect_nondep
    (fun _ => Return (@None unit))
    (fun _ rec maps =>
       let (m,tr) := maps : _ * Map (coro_type readWrite_step) in
       osa <- newAccept tt;
         match osa with
         | Some sa =>
           pipe (readWrite fuel' certs keys : coro_type readWrite_step)
                (fun c =>
                   ef <- resume c $ inhabitant;
                     _ <- perform (sa, ef);
                     let tr' := insert sa c tr in
                     rec (m, tr'))
         | None =>
           o <- receive tt;
             match o with
             | None => rec (m,tr)
             | Some (sa,r) =>
               let ocoro := bsearch sa tr in
               match ocoro with
               | Some coro =>
                 ef <- resume coro $ r;
                 match isSetPSK ef with
                 | Some (sid,sess) =>
(*                 | inl (inl (inl (inl (inl (inl (inl (inl (sid, sess)))))))) => *)
                   let m' := insert sid sess m in
                   ef <- resume coro $ (inl (inr tt));
                   _ <- perform (sa, ef);
                   let tr' := replace_map sa coro tr in
                   rec (m', tr')
                 | None =>
                   match isSessionResume ef with
                   | Some sid =>
(*                 | inl (inl (inl (inl (inl (inl (inl (inr sid))))))) =>*)
                     let (sess,m') := lookupAndDelete sid m in
                     ef <- resume coro $ (inl (inl (inl (inl (inl sess)))));
                     _ <- perform (sa, ef);
                     let tr' := replace_map sa coro tr in
                     rec (m', tr')
                   | None =>
(*                 | _ => *)
                     _ <- perform (sa,ef);
                     let tr' := replace_map sa coro tr in
                     rec (m, tr')
                   end
                 end
               | None => Return None
               end
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
  | @bind ?T ?S ?eff ?args ?rets ?p ?f =>
    let x :=  (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy' (S i) x in
    lazymatch (eval pattern (dummy _ T i) in d) with
    | ?g _ =>
      constr:((@bind T S eff args rets p, g))
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
  | (@bind ?T ?S ?eff ?args ?rets ?p, ?g) =>
    let x := (eval cbv beta in (g (dummy _ _ i))) in
    let q := reconstruct' x (S i) in
    lazymatch (eval pattern (dummy _ T i) in q) with
    | ?g' _ =>
      constr:(@bind T S eff args rets p g')
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

Definition main_loop_derive  :
  { state & { step & forall fuel fuel' certs keys,
                { init | @equiv _ _ _ _ state step init (main_loop fuel fuel' certs keys) }}}.
Proof.
  do 3 eexists.

  lazymatch goal with
    |- equiv _ ?init ?x =>
    let u := open_constr:(inl (tt,fuel,fuel',certs,keys)) in
    unify init u;
    let H := fresh in
    assert (x = ltac:(let x' := eval red in x in
                          let x'' := coro_to_state' x' in exact x''))
      as H by
         (change x with ltac:(let x0 := eval red in x in exact x0);
            unfold pipe, sum_merge;
            repeat mid_eq_core)
  end.
  
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
Extract Inductive CPacket => "I.Packet13" ["I.Handshake13" "I.ChangeCipherSpec13" "I.AppData13"].
Extract Inductive Header => "I.Header" ["I.Header"].
Extract Inductive CServerRandom => "I.ServerRandom" ["I.ServerRandom"].
Extract Inductive CClientRandom => "I.ClientRandom" ["I.ClientRandom"].
Extract Inductive SessionData => "I.SessionData" ["I.SessionData"].
Extract Inductive SessionFlag =>"I.SessionFlag" ["I.SessionEMS"].
Extract Inductive PskIdentity => "I.PskIdentity" ["I.PskIdentity"].
Extract Inductive PreSharedKey => "I.PreSharedKey" ["I.PreSharedKeyClientHello" "I.PreSharedKeyServerHello"].
Extract Inductive PskKexMode => "I.PskKexMode" ["I.PSK_KE" "I.PSK_DHE_KE"].
Extract Constant ProtocolType => "I.ProtocolType".
Extract Constant decodeRecord => "Helper.decodeRecord".
Extract Constant decodeHeader => "\bs -> case I.decodeHeader bs of { Prelude.Right x -> x }".
Extract Constant Certificate => "X.Certificate".
Extract Constant CertificateChain => "X.CertificateChain".
Extract Constant getCertificates => "\cch -> case cch of { X.CertificateChain certs -> Prelude.map X.getCertificate certs }".
Extract Constant HashAndSignatureAlgorithm => "I.HashAndSignatureAlgorithm".
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
Extract Constant handshake13 => "I.Handshake13".
Extract Constant serverHello13 => "(\b -> I.ServerHello13 (I.ServerRandom {I.unServerRandom = b}))".

Extract Constant extension_KeyShare =>
"(\exts -> case Helper.extensionLookup I.extensionID_KeyShare exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.KeyShareClientHello kses) -> GHC.Base.return kses})".
Extract Constant serverGroups => "Helper.serverGroups".
Extract Constant changeCipherSpec => "\p -> case p of { I.ChangeCipherSpec13 -> GHC.Base.Just (); _ -> GHC.Base.Nothing }".
Extract Constant extension_SignatureAlgorithms =>
"(\exts -> case Helper.extensionLookup I.extensionID_SignatureAlgorithms exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.SignatureAlgorithms sas) -> sas })".
Extract Constant defaultCertChain => "Helper.defaultCertChain".
Extract Constant certificate13 => "I.Certificate13".
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
Extract Constant encryptedExtensions13 => "I.EncryptedExtensions13".
Extract Constant sniExt => "Helper.sniExt".
Extract Constant CryptoError => "I.CryptoError".
Extract Constant encodeGroupPublic => "I.encodeGroupPublic".
Extract Constant decodeGroupPublic => "\g bs -> case I.decodeGroupPublic g bs of { Prelude.Right a -> GHC.Base.Just a; _ -> GHC.Base.Nothing }".
Extract Constant ba_convert => "BA.convert".
Extract Constant hashDigestSize => "I.hashDigestSize".
Extract Constant Word8 => "Data.Word8.Word8".
Extract Constant b_replicate => "B.replicate".
Extract Constant w0 => "Data.Word8._nul".
Extract Constant hkdfExtract => "I.hkdfExtract".
Extract Constant hkdfExpandLabel => "I.hkdfExpandLabel".
Extract Constant s2b => "(\s -> B.pack (Prelude.map (\c -> Prelude.fromIntegral (Data.Char.ord c)) s))".
Extract Constant b2s => "(\b -> Prelude.map Data.ByteString.Internal.w2c (B.unpack b))".
Extract Constant GroupKey => "I.GroupKey".
Extract Constant GroupPublic => "I.GroupPublic".
Extract Constant finished13 => "I.Finished13".
Extract Constant hmac => "I.hmac".
Extract Constant ByteString_beq => "(GHC.Base.==)".
Extract Constant appData13 => "I.AppData13".
Extract Constant isDigitalSignaturePair => "I.isDigitalSignaturePair".
Extract Constant signatureCompatible13 => "I.signatureCompatible13".
Extract Constant certPubKey => "X.certPubKey".
Extract Constant Word32 => "Data.Word.Word32".
Extract Constant Signature => "I.Signature".
Extract Constant KeyUpdate => "I.KeyUpdate".
Extract Constant Bsplit => "B.splitAt".
Extract Constant Blength => "B.length".
Extract Constant Hash_beq => "(GHC.Base.==)".
Extract Constant ExtensionRaw_PreSharedKey =>
"I.ExtensionRaw I.extensionID_PreSharedKey".
Extract Constant CompressionID => "Data.Word8.Word8".
Extract Constant TicketInfo => "T.TLS13TicketInfo".
Extract Constant encodeHandshake13 => "I.encodeHandshake13".
Extract Constant extension_PreSharedKey =>
"\exts -> Helper.extensionLookup I.extensionID_PreSharedKey exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello".
Extract Constant nat2Word32 => "Prelude.fromIntegral".
Extract Constant extension_PskKeyModes =>
"(\exts -> case Helper.extensionLookup I.extensionID_PskKeyExchangeModes exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.PskKeyExchangeModes ms) -> GHC.Base.return ms; GHC.Base.Nothing -> []})".
Extract Constant Btake => "B.take".
Extract Constant dummyCompressionID => "Prelude.fromIntegral 0".
Extract Constant packet2tinfo => "Helper.packet2tinfo".
Extract Constant extensionEncode_PreSharedKey => "I.extensionEncode".
Extract Constant lifetime => "172800".
Extract Constant addAge => "100000".

Require Extraction.
Extraction Language Haskell.

Extraction "TLS.hs" main_loop_step.
