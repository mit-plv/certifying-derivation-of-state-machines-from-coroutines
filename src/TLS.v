Require Import List.
Require String.
Require Import Inhabit Foldable ClConv.
Import ListNotations.
Import String.StringSyntax.
Open Scope string_scope.

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
  { ksGroup : Group;
    ksData : ByteString
  }.

Parameter ExtensionRaw : Set.
Parameter Session : Set.
Parameter CipherID : Set.
Parameter Version : Set.

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
    match find (fun k => Group_beq (ksGroup k) g) ks with
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
Parameter PublicKey PrivateKey : Set.
Parameter GroupPublic GroupKey : Set.
Parameter Hash Cipher HashAndSignatureAlgorithm : Set.

Inductive eff_tls := recvClientHello | recvFinished | recvCCS | recvAppData | getRandomBytes | sendPacket | groupGetPubShared | makeCertVerify.

Definition args_tls ef :=
  match ef with
  | recvClientHello => unit
  | recvFinished => option (Hash * Cipher * ByteString)
  | recvCCS => unit
  | recvAppData => option (Hash * Cipher * ByteString)
  | getRandomBytes => nat
  | sendPacket => Packet13 * option (Hash * Cipher * ByteString * nat)
  | groupGetPubShared => GroupPublic
  | makeCertVerify => PublicKey * PrivateKey * (HashAndSignatureAlgorithm) * ByteString
  end.

Definition rets_tls ef :=
  match ef with
  | recvClientHello => ClientHelloMsg * ByteString
  | recvFinished => ByteString
  | recvCCS => unit
  | recvAppData => ByteString
  | getRandomBytes => ByteString
  | sendPacket => ByteString
  | groupGetPubShared => option (GroupPublic * GroupKey)
  | makeCertVerify => Handshake13
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
  | recvFinished =>
    fun a0 : rets_tls recvFinished -> A + option B =>
      match e0 as e1 return (rets_tls e1 -> A + option B) with
      | recvFinished => a0
      | _ => fun _ => inr None
      end
  | recvCCS =>
    fun a0 : rets_tls recvCCS -> A + option B =>
      match e0 as e1 return (rets_tls e1 -> A + option B) with
      | recvCCS => a0
      | _ => fun _ => inr None
      end
  | recvAppData =>
    fun a0 : rets_tls recvAppData -> A + option B =>
      match e0 as e1 return (rets_tls e1 -> A + option B) with
      | recvAppData => a0
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
  | groupGetPubShared =>
    fun a0 : rets_tls groupGetPubShared -> A + option B =>
      match e0 as e1 return (rets_tls e1 -> A + option B) with
      | groupGetPubShared => a0
      | _ => fun _ => inr None
      end
  | makeCertVerify =>
    fun a0 : rets_tls makeCertVerify -> A + option B =>
      match e0 as e1 return (rets_tls e1 -> A + option B) with
      | makeCertVerify => a0
      | _ => fun _ => inr None
      end
  end a.

Instance eff_tls_is_eff : is_eff eff_tls :=
  { args := args_tls;
    rets := rets_tls;
    lift_eff := lift_tls }.

Notation "r <- ef a ; p" :=
  (@Eff eff_tls args_tls rets_tls _ ef a (fun r => p))
    (at level 100, ef at level 0, right associativity).

(*
Notation "ch <-recvClientHello ctx ; p" :=
  (@Eff eff_tls args_tls rets_tls _ recvClientHello ctx (fun ch => p))
    (at level 100, right associativity).

Notation "v <-recvFinished tt ; p" :=
  (@Eff eff_tls args_tls rets_tls _ recvFinished tt (fun v => p))
    (at level 100, right associativity).

Notation "v <-recvCCS tt ; p" :=
  (@Eff eff_tls args_tls rets_tls _ recvCCS tt (fun v => p))
    (at level 100, right associativity).

Notation "b <-getRandomBytes n ; p" :=
  (@Eff eff_tls args_tls rets_tls _ getRandomBytes n (fun b => p))
    (at level 100, right associativity).

Notation "b <-sendPkt pkt ; p" :=
  (@Eff eff_tls args_tls rets_tls _ sendPacket pkt (fun b => p))
    (at level 100, right associativity).

Notation "keys <-genKeys ; p" :=
  (@Eff eff_tls args_tls rets_tls _ genKeys tt (fun keys => p))
    (at level 100, right associativity).

Notation "pair <-groupGetPubShared pub ; p" :=
  (@Eff eff_tls args_tls rets_tls _ groupGetPubShared pub (fun pair => p))
    (at level 100, right associativity).
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
Parameter serverSupportedCiphers : ServerParams -> list Cipher.
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
Parameter changeCipherSpec : Packet13.
Parameter extension_SignatureAlgorithms : list ExtensionRaw -> list (HashAndSignatureAlgorithm).

Parameter Certificate CertificateChain : Set.
Parameter getCertificates : CertificateChain -> list Certificate.
Parameter defaultCertChain : PublicKey -> CertificateChain.
Parameter certificate13 : ByteString -> CertificateChain -> list (list ExtensionRaw) -> Handshake13.
Parameter empty : ByteString.
Parameter ciphersuite_default : list Cipher.
Parameter encodePacket13 : Packet13 -> ByteString.
Parameter hashWith : Hash -> list ByteString -> ByteString.
Parameter encryptedExtensions13 : list ExtensionRaw -> Handshake13.
Parameter sniExt : ExtensionRaw.
Parameter appData13 : ByteString -> Packet13.
Parameter encodeEncryptedExt : list ExtensionRaw -> ByteString.
Parameter CryptoError : Set.
Parameter encodeGroupPublic : GroupPublic -> ByteString.
Parameter decodeGroupPublic : Group -> ByteString -> CryptoError + GroupPublic.
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

Definition doHandshake (cch: CertificateChain)(pr: PrivateKey) :=
  chr <- recvClientHello tt;
  let certs := getCertificates cch in
  let ch := fst chr in
  let chEncoded := snd chr in
  match chooseCipher (chCiphers ch) serverCiphers with
  | None => Return (Some "no cipher available")
  | Some cipher =>
    let opt := extension_KeyShare ch.(chExtension) in
    match opt with
    | None => Return (Some "no keyshare")
    | Some keyShares =>
      let oks := findKeyShare keyShares serverGroups in
      match oks with
      | None => Return (Some "no keyshare available")
      | Some keyShare =>
        let ecpub := decodeGroupPublic (ksGroup keyShare) (ksData keyShare) in
        match ecpub with
        | inl _ => Return (Some "no group")
        | inr cpub =>
          mecdhePair <- groupGetPubShared cpub;
          match mecdhePair with
          | None => Return (Some "generating ECDHE pair failed")
          | Some ecdhePair =>
            let wspub := encodeGroupPublic (fst ecdhePair) in
            let ecdhe := ba_convert (snd ecdhePair) in
            let serverKeyShare := {| ksGroup := (ksGroup keyShare); ksData := wspub |} in
            
            (* sendServerHello *)
            let ks := extensionEncode_KeyShare serverKeyShare in
            let selectedVersion := extensionEncode_SupportedVersions TLS13 in
            let extensions' :=
                [ extensionRaw_KeyShare ks;
                    extensionRaw_SupportedVersions selectedVersion ]
            in
            srand <- getRandomBytes 32;
            shEncoded <- sendPacket (handshake13 [serverHello13 srand (chSession ch) (cipherID cipher) extensions'], None);
            let usedHash := cipherHash cipher in
            let hCh := hashWith usedHash [chEncoded; shEncoded] in
            let hsize := hashDigestSize usedHash in
            let zero := b_replicate hsize w0 in
            let earlySecret := hkdfExtract usedHash zero zero in
            let clientEarlySecret := hkdfExpandLabel usedHash earlySecret (s2b "c e traffic") hCh hsize in
            
            let handshakeSecret := hkdfExtract usedHash (hkdfExpandLabel usedHash earlySecret (s2b "derived") (hashWith usedHash [s2b ""]) hsize) ecdhe in
            let clientHandshakeSecret := hkdfExpandLabel usedHash handshakeSecret (s2b "c hs traffic") hCh hsize in
            let serverHandshakeSecret := hkdfExpandLabel usedHash handshakeSecret (s2b "s hs traffic") hCh hsize in
            ccsEncoded <- sendPacket (changeCipherSpec, None);
            extEncoded <- sendPacket (handshake13 [encryptedExtensions13 []], Some (usedHash, cipher, serverHandshakeSecret, 0));

            let hashSigs := extension_SignatureAlgorithms ch.(chExtension) in
            let mcred := decideCredInfo pr certs hashSigs in
            match mcred with
            | None => Return None
            | Some pubhs =>
              let pub := fst pubhs in
              let hashSig := snd pubhs in
              certEncoded <- sendPacket (handshake13 [certificate13 empty cch [[]]], Some (usedHash, cipher, serverHandshakeSecret, 1));
              let hashed := hashWith (cipherHash cipher) [chEncoded; shEncoded; extEncoded; certEncoded] in
              cv <- makeCertVerify (pub,pr,hashSig,hashed);
              cvEncoded <- sendPacket (handshake13 [cv], Some (usedHash, cipher, serverHandshakeSecret, 2));
              let hashed' := hashWith (cipherHash cipher) [chEncoded; shEncoded; extEncoded; certEncoded; cvEncoded] in
              finEncoded <- sendPacket (handshake13 [finished13 (makeVerifyData usedHash serverHandshakeSecret hashed')], Some (usedHash, cipher, serverHandshakeSecret, 3));

              let hashed'' := hashWith (cipherHash cipher) [chEncoded; shEncoded; extEncoded; certEncoded; cvEncoded; finEncoded] in
              let applicationSecret := hkdfExtract usedHash (hkdfExpandLabel usedHash handshakeSecret (s2b "derived") (hashWith usedHash [s2b ""]) hsize) zero in
              let clientApplicationSecret := hkdfExpandLabel usedHash applicationSecret (s2b "c ap traffic") hashed'' hsize in
              let serverApplicationSecret := hkdfExpandLabel usedHash applicationSecret (s2b "s ap traffic") hashed'' hsize in

              _ <- recvCCS tt;
              fin <- recvFinished (Some (usedHash, cipher, clientHandshakeSecret));
              if ByteString_beq fin (makeVerifyData usedHash clientHandshakeSecret hashed'') then
                nat_rect_nondep
                  (fun _ => Return (Some "success"))
                  (fun _ rec _ =>
                     data <- recvAppData (Some (usedHash, cipher, clientApplicationSecret));
                       _ <- sendPacket (appData13 (mconcat ([s2b ("HTTP/1.1 200 OK" ++ CR ++ LF ++ "Content-Type: text/plain" ++ CR ++ LF ++ CR ++ LF ++ "Hello, "); data; s2b ("!" ++ CR ++ LF)] ++ replicate 1000 (s2b ".."))), Some (usedHash, cipher, serverApplicationSecret, 0));
                     (rec tt))
                  5 tt
              else Return None
            end
          end
        end
      end
    end
  end.

Definition doHandshake_derive :
  { state & { step &
              forall certs priv,
                { init | @equiv _ _ _ _ state step init (doHandshake certs priv) }}}.
Proof.
  do 3 eexists.
  unfold doHandshake.
  derive' (tt, certs, priv).
Defined.

Definition doHandshake_step := Eval cbv [projT1 projT2 doHandshake doHandshake_derive] in (projT1 (projT2 doHandshake_derive)).

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
Extract Constant Certificate => "X.Certificate".
Extract Constant CertificateChain => "X.CertificateChain".
Extract Constant getCertificates => "\cch -> case cch of { X.CertificateChain certs -> Prelude.map X.getCertificate certs }".
Extract Constant HashAndSignatureAlgorithm => "I.HashAndSignatureAlgorithm".
Extract Constant Group_eq_dec => "(GHC.Base.==)".
Extract Constant Group_beq => "(GHC.Base.==)".
Extract Constant Context => "T.Context".
Extract Constant ExtensionRaw => "I.ExtensionRaw".
Extract Constant Session => "I.Session".
Extract Constant CipherID => "T.CipherID".
Extract Constant Handshake13 => "I.Handshake13".
Extract Constant Packet13 => "I.Packet13".
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
Extract Constant changeCipherSpec => "I.ChangeCipherSpec13".
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
Extract Constant decodeGroupPublic => "I.decodeGroupPublic".
Extract Constant ba_convert => "BA.convert".
Extract Constant hashDigestSize => "I.hashDigestSize".
Extract Constant Word8 => "Data.Word8.Word8".
Extract Constant b_replicate => "B.replicate".
Extract Constant w0 => "Data.Word8._nul".
Extract Constant hkdfExtract => "I.hkdfExtract".
Extract Constant hkdfExpandLabel => "I.hkdfExpandLabel".
Extract Constant s2b => "(\s -> B.pack (Prelude.map (\c -> Prelude.fromIntegral (Data.Char.ord c)) s))".
Extract Constant GroupKey => "I.GroupKey".
Extract Constant GroupPublic => "I.GroupPublic".
Extract Constant finished13 => "I.Finished13".
Extract Constant hmac => "I.hmac".
Extract Constant ByteString_beq => "(GHC.Base.==)".
Extract Constant appData13 => "I.AppData13".
Extract Constant isDigitalSignaturePair => "I.isDigitalSignaturePair".
Extract Constant signatureCompatible13 => "I.signatureCompatible13".
Extract Constant certPubKey => "X.certPubKey".

(*
Extract Constant extension_KeyShare => "Helper.extension_KeyShare".
Extract Constant extension_NegotiatedGroups => "Helper.extension_NegotiatedGroups".
Extract Constant serverGroups => "Helper.serverGroups".
Extract Inductive KeyShare => "Helper.KeyShare" ["Helper.Build_KeyShare"].
 *)

Require Extraction.
Extraction Language Haskell.

Extraction "TLS.hs" doHandshake_step.
