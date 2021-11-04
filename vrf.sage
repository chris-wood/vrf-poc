#!/usr/bin/sage
# vim: syntax=python

'''
Note: I did not check the RSA-based VRF test vectors or pseudocode closely.

# Specific comments

- Section 3: Many of the security properties have "weaker" versions (trusted 
  uniqueness, trusted collision resistance, etc) and claims that these are 
  sufficient for many applications. It is not clear under what conditions 
  applications require stronger variants. Perhaps this should be added to
  the security considerations?
- Section 3.4: Do we have proofs that the schemes in this document satisfy 
  the RO-like property, or is this merely intuitively true? If the former,
  perhaps we should note that this analysis remains to be done?
- Section 4/5: Unless I'm missing something, neither the RSA-baed VRF has no
  variant for achieving "full" security, unlike the ECVRF, which depends on the
  procedures in Section 5.6. Should this inconsistency be noted in the introduction?
- Section 5. "Note that with certain software libraries (for big integer and
      elliptic curve arithmetic), the int_to_string and point_to_string
      conversions are not needed" --> it seems worth clarifying that this is
  is true iff the libraries return strings that are encoded in the same way
  as required by the corresponding ciphersuites, for interoperability reasons.
- Section 5.3. It might be worth noting that the verification check does not
  need to be done in constant time as it's a public operation. (The comparison
  check at the end might lead one to ask whether or not it needs to be constant
  time, so calling it out early would clarify.)
- Section 5.4.4. Remove "let" in "let <variable> = ..." statements, as this
  is not done in other functions where variables are declared and initialized.
- Section 5.6. It's noted that the procedure in this section does not work if either
  the curve or generator are untrusted, but aren't these both fixed for the suites
  in this document? If so, I might remove this paragraph.
- Section 5.6.1. Do implementations for curves with small cofactors perform validation
  by checking against known points? I don't know! If this isn't common, I would simply 
  remove the variant for ed25519, as it just seems simpler to clear the cofactor and 
  check against the identity element. Conversely, the hash-to-curve document has specific 
  cofactor clearing suggestions for each curve, and it seems reasonable to be opinionated in
  this document, too. One might even just re-use the methods in draft-irtf-cfrg-hash-to-curve
  for P-256 and ed25519.
- Section 7.1. Recommendations for randomness generation can probably be cribbed
  from https://datatracker.ietf.org/doc/html/rfc8446#appendix-C.1. 

# General comments

- Can we remove try-and-increment entirely from this specification? The security 
  relevant discussion in 7.4 can be easily skipped by applications looking to implement
  one of the options in either 5.4.1.1 or 5.4.1.2.
- In some places the public key is denoted as Y (Section 7.1.1), but in others it's 
  denoted as PK. Perhaps these should be consistent?

'''

import sys
import hashlib
import hmac
import binascii

from hash_to_field import I2OSP, OS2IP

if sys.version_info[0] == 3:
    xrange = range
    def _as_bytes(x): return x if isinstance(x, bytes) else bytes(x, "utf-8")
    def _strxor(str1, str2): return bytes(
        s1 ^ s2 for (s1, s2) in zip(str1, str2))
else:
    def _as_bytes(x): return x
    def _strxor(str1, str2): return ''.join(chr(ord(s1) ^ ord(s2))
                                            for (s1, s2) in zip(str1, str2))

try:
    from sagelib.groups import GroupP256NU
except ImportError:
    sys.exit("Error loading preprocessed sage files. Try running `make clean pyfiles`")

def int_to_string(i, n):
    return I2OSP(i, n)

def string_to_int(s):
    return OS2IP(s)

class ECVRF(object):
    def __init__(self, G, H, suite_string, h2c_suite):
        self.G = G
        self.H = H
        self.n = ceil(G.field_bytes_length / 2)
        self.ptLen = 1 + G.field_bytes_length
        self.qLen = ceil(log(G.order(), 2) / 8)
        self.hLen = H().digest_size
        self.suite_string = suite_string
        self.h2c_suite_ID_string = h2c_suite
        self.cofactor = 1 # XXX(caw): inherit from G

    def point_to_string(self, x):
        return self.G.serialize(x)

    def string_to_point(self, p):
        return self.G.deserialize(p)

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.1
    def prove(self, SK, alpha_string):
        x = SK
        n = self.n
        qLen = self.qLen
        q = self.G.order()
        B = self.G.generator()

        Y = x * self.G.generator()
        H = self.hash_to_curve(Y, alpha_string)
        h_string = self.point_to_string(H)
        Gamma = x * H
        k = self.nonce_generation(SK, h_string)
        c = self.hash_points([H, Gamma, k * B, k * H])
        s = (k + (c * x)) % q

        pi_string = self.point_to_string(Gamma) + int_to_string(c, n) + int_to_string(s, qLen)

        return pi_string

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.2
    def proof_to_hash(self, pi_string):
        (Gamma, _, s) = self.decode_proof(pi_string)
        three_string = int_to_string(3, 1)
        zero_string = int_to_string(0, 1)

        hasher = self.H()
        hasher.update(self.suite_string)
        hasher.update(three_string)
        hasher.update(self.point_to_string(self.cofactor * Gamma))
        hasher.update(zero_string)
        beta_string = hasher.digest()

        return beta_string

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.3
    def verify(self, Y, pi_string, alpha_string):
        B = self.G.generator()
        (Gamma, c, s) = self.decode_proof(pi_string)
        H = self.hash_to_curve(Y, alpha_string)
        U = (s * B) - (c * Y)
        V = (s * H) - (c * Gamma)
        c_prime = self.hash_points([H, Gamma, U, V])
        return c == c_prime

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.4.1.2
    def hash_to_curve(self, Y, alpha_string):
        PK_string = self.point_to_string(Y)
        string_to_hash = PK_string + alpha_string
        H = self.encode(string_to_hash)
        return H

    def encode(self, msg):
        DST = _as_bytes("ECVRF_") + self.h2c_suite_ID_string + self.suite_string
        H = self.G.hash_to_group(msg, DST)
        return H

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.4.2
    def nonce_generation(self, SK, h_string):
        raise Exception("Not implemented")

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.4.3
    def hash_points(self, points):
        two_string = int_to_string(2, 1)
        hash_str = self.suite_string + two_string
        for p_j in points:
            hash_str = hash_str + self.point_to_string(p_j)
        zero_string = int_to_string(0, 1)
        hash_str = hash_str + zero_string

        hasher = self.H()
        hasher.update(hash_str)
        c_string = hasher.digest()
        truncated_c_string = c_string[0:self.n]
        c = string_to_int(truncated_c_string)
        return c

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.4.4
    def decode_proof(self, pi_string):
        gamma_string = pi_string[0:self.ptLen]
        c_string = pi_string[self.ptLen:self.ptLen+self.n]
        s_string = pi_string[self.ptLen+self.n:self.ptLen+self.n+self.qLen]
        Gamma = self.string_to_point(gamma_string)
        c = string_to_int(c_string)
        s = string_to_int(s_string)
        return (Gamma, c, s)

# ECVRF-P256-SHA256-SSWU, P256_XMD:SHA-256_SSWU_NU_
class ECVRFP256(ECVRF):
    def __init__(self):
        ECVRF.__init__(self, GroupP256NU(), hashlib.sha256, int_to_string(2, 1), _as_bytes("P256_XMD:SHA-256_SSWU_NU_"))

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.4.2.1 for p256
    def nonce_generation(self, SK, h_string):
        m = h_string
        x = SK
        q = self.G.order()
        qlen = log(q) / log(2)

        def bits2int(b):
            # https://datatracker.ietf.org/doc/html/rfc6979#section-2.3.2
            if self.qLen < len(b):
                return OS2IP(b[0:self.qLen])
            else:
                while self.qLen > len(b):
                    b = b + bytes([0x00])
                return OS2IP(b)
        def int2octets(m):
            # https://datatracker.ietf.org/doc/html/rfc6979#section-2.3.3
            return int_to_string(m, self.qLen)
        def bits2octets(b):
            # https://datatracker.ietf.org/doc/html/rfc6979#section-2.3.4
            z1 = bits2int(b)
            z2 = z1 % q
            return int2octets(z2)

        # a. h1 = H(m)
        hasher = self.H()
        hasher.update(m)
        h1 = hasher.digest()

        # b. V = 0x01 0x01 0x01 ... 0x01
        V = bytes([0x01] * self.hLen)
        # c. K = 0x00 0x00 0x00 ... 0x00
        K = bytes([0x00] * self.hLen)
        
        # d. K = HMAC_K(V || 0x00 || int2octets(x) || bits2octets(h1))
        K = hmac.digest(K, V + bytes([0x00]) + int2octets(x) + bits2octets(h1), self.H)
        # e. V = HMAC_K(V)
        V = hmac.digest(K, V, self.H)
        # f. K = HMAC_K(V || 0x01 || int2octets(x) || bits2octets(h1))
        K = hmac.digest(K, V + bytes([0x01]) + int2octets(x) + bits2octets(h1), self.H)
        # g. V = HMAC_K(V)
        V = hmac.digest(K, V, self.H)
        
        # h. Apply the following algorithm until a proper value is found for k:
        while True:
            T = bytes([])
            while len(T)*8 < qlen:
                V = hmac.digest(K, V, self.H)
                T = T + V

            k = bits2int(T)
            if 1 <= k and k <= q - 1:
                return k
            
            # K = HMAC_K(V || 0x00)
            K = hmac.digest(K, V + bytes([0x00]), self.H)
            # V = HMAC_K(V)
            V = hmac.digest(K, V, self.H)

# ECVRF-EDWARDS25519-SHA512-ELL2, edwards25519_XMD:SHA-512_ELL2_NU_
class ECVRFEd25519(ECVRF):
    def __init__(self):
        ECVRF.__init__(self, GroupEd25519(), hashlib.sha512, int_to_string(4, 1), _as_bytes("edwards25519_XMD:SHA-512_ELL2_NU_"))

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.4.2.2
    def nonce_generation(self, SK, h_string):
        # 1.  hashed_sk_string = Hash(SK)
        hasher = self.H()
        hasher.update(SK)
        hashed_sk_string = hasher.digest()

        # 2.  truncated_hashed_sk_string = hashed_sk_string[32]...hashed_sk_string[63]
        truncated_hashed_sk_string = hashed_sk_string[32:]

        # 3.  k_string = Hash(truncated_hashed_sk_string || h_string)
        hasher = self.H()
        hasher.update(truncated_hashed_sk_string)
        hasher.update(h_string)
        k_string = hasher.digest()

        # 4.  k = string_to_int(k_string) mod q
        q = self.G.order()
        k = string_to_int(k_string) % q

        return k

vrf_vectors = [
    {
        # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#appendix-A.2
        "vrf": ECVRFP256,
        "tests": [
            {
                "SK": "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721",
                "PK": "0360fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6",
                "alpha": "73616d706c65",
                "H": "02b31973e872d4a097e2cfae9f37af9f9d73428fde74ac537dda93b5f18dbc5842",
                "k": "e92820035a0a8afe132826c6312662b6ea733fc1a0d33737945016de54d02dd8",
                "U": "031490f49d0355ffcdf66e40df788bee93861917ee713acff79be40d20cc91a30a",
                "V": "03701df0228138fa3d16612c0d720389326b3265151bc7ac696ea4d0591cd053e3",
                "pi": "0331d984ca8fece9cbb9a144c0d53df3c4c7a33080c1e02ddb1a96a365394c7888a39dfe7432f119228473f37db3f87ca470c63b0237432a791f18f823c1215e276b7ac0962725ba8daec2bf90c0ccc91a",
                "beta": "21e66dc9747430f17ed9efeda054cf4a264b097b9e8956a1787526ed00dc664b"
            },
            {
                "SK": "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721",
                "PK": "0360fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6",
                "alpha": "74657374",
                "H" : "03ccc747fa7318b9486ce4044adbbecaa084c27be6eda88eb7b7f3d688fd0968c7",
                "k": "febc3451ea7639fde2cf41ffd03f463124ecb3b5a79913db1ed069147c8a7dea",
                "U": "031200f9900e96f811d1247d353573f47e0d9da601fc992566234fc1a5b37749ae",
                "V": "02d3715dcfee136c7ae50e95ffca76f4ca6c29ddfb92a39c31a0d48e75c6605cd1",
                "pi": "03f814c0455d32dbc75ad3aea08c7e2db31748e12802db23640203aebf1fa8db2721e0499b7cecd68027a82f6095da076625a5f2f62908f1c283d5ee9b9e852d85bedf64f2452a4e5094729e101824443e",
                "beta": "8e7185d2b420e4f4681f44ce313a26d05613323837da09a69f00491a83ad25dd",
            },
            {
                "SK": "2ca1411a41b17b24cc8c3b089cfd033f1920202a6c0de8abb97df1498d50d2c8",
                "PK": "03596375e6ce57e0f20294fc46bdfcfd19a39f8161b58695b3ec5b3d16427c274d",
                "alpha": "4578616d706c65207573696e67204543445341206b65792066726f6d20417070656e646978204c2e342e32206f6620414e53492e58392d36322d32303035",
                "H": "022dd5150e5a2a24c66feab2f68532be1486e28e07f1b9a055cf38ccc16f6595ff",
                "k": "8e29221f33564f3f66f858ba2b0c14766e1057adbd422c3e7d0d99d5e142b613",
                "U": "03a8823ff9fd16bf879261c740b9c7792b77fee0830f21314117e441784667958d",
                "V": "02d48fbb45921c755b73b25be2f23379e3ce69294f6cee9279815f57f4b422659d",
                "pi": "039f8d9cdc162c89be2871cbcb1435144739431db7fab437ab7bc4e2651a9e99d5288aac70a5e4bd07df303c1d460eb6336bb5fa95436a07c2f6b7aec6fef7cc4846ea901ee1e238dee12bf752029b0b2e",
                "beta": "4fbadf33b42a5f42f23a6f89952d2e634a6e3810f15878b46ef1bb85a04fe95a",
            }
        ]
    },
]

signature_vectors = [{
    # https://datatracker.ietf.org/doc/html/rfc6979#appendix-A.2.5
    "vrf": ECVRFP256,
    "tests": [
        {
            "x": "C9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721",
            "k": "A6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60",
            "msg": "sample",
        }
    ]
}]

if __name__ == "__main__":
    for vector in vrf_vectors:
        for t in vector["tests"]:
            vrf = vector["vrf"]()
            SK = string_to_int(binascii.unhexlify(t["SK"]))
            PK = vrf.G.deserialize(binascii.unhexlify(t["PK"]))
            alpha_string = binascii.unhexlify(t["alpha"])
            beta_string_expected = binascii.unhexlify(t["beta"])
            pi_string_expected = binascii.unhexlify(t["pi"])

            pi_string = vrf.prove(SK, alpha_string)
            beta_string = vrf.proof_to_hash(pi_string)
            valid = vrf.verify(PK, pi_string, alpha_string)
            assert(pi_string == pi_string_expected)
            assert(beta_string == beta_string_expected)
            assert(valid)

    for vector in signature_vectors:
        for t in vector["tests"]:
            vrf = vector["vrf"]()
            x = string_to_int(binascii.unhexlify(t["x"]))
            expected_k = string_to_int(binascii.unhexlify(t["k"]))
            k = vrf.nonce_generation(x, _as_bytes(t["msg"]))
            assert(k == expected_k)
            
