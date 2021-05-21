#!/usr/bin/sage
# vim: syntax=python

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
    print("Importing modules...")
    from sagelib.groups import GroupP256NU
except ImportError:
    sys.exit("Error loading preprocessed sage files. Try running `make clean pyfiles`")

def int_to_string(i, n):
    print(type(i), type(n))
    return I2OSP(i, n)

def string_to_int(s):
    return OS2IP(s)

class ECVRF(object):
    def __init__(self, G, H, suite_string, h2c_suite):
        self.G = G
        self.H = H
        # XXX(caw): check that these parameters are correct
        self.n = ceil(G.field_bytes_length / 2)
        self.ptLen = 1 + G.field_bytes_length
        self.qLen = ceil(log(G.order(), 2) / 8)
        self.hLen = H().digest_size
        self.suite_string = suite_string
        self.h2c_suite_ID_string = h2c_suite
        self.cofactor = 1 # XXX(caw): inherit from G?

        print("n", self.n)
        print("ptLen", self.ptLen)
        print("qLen", self.qLen)
        print("hLen", self.hLen)

    def point_to_string(self, x):
        return self.G.serialize(x)

    def string_to_point(self, p):
        return self.G.deserialize(p)

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.1
    def prove(self, SK, alpha_string):
        x = SK # the secret key is the scalar
        n = self.n
        qLen = self.qLen
        B = self.G.generator()

        Y = x * self.G.generator()
        print("PK", binascii.hexlify(self.G.serialize(Y)))
        H = self.hash_to_curve(Y, alpha_string)
        print("H", binascii.hexlify(self.G.serialize(H)))
        h_string = self.point_to_string(H)
        Gamma = x * H
        k = self.nonce_generation(SK, h_string)
        print("k", binascii.hexlify(int_to_string(k, qLen)))
        c = self.hash_points([H, Gamma, k * B, k * H])
        s = (k + (c * x)) % self.G.order()
        pi_string = self.point_to_string(Gamma)
        pi_string = pi_string + int_to_string(c, n)
        pi_string = pi_string + int_to_string(s, qLen)
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
        print("DST", DST)
        H = self.G.hash_to_group(msg, DST)
        return H

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.4.2
    def nonce_generation(self, SK, h_string):
        pass

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
        # XXX(caw): remove "let ... = " in draft
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
        # XXX(caw): this is terrible and awful...
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
        print("h1", binascii.hexlify(h1))

        # b. V = 0x01 0x01 0x01 ... 0x01
        V = bytes([0x01] * self.hLen)
        # c. K = 0x00 0x00 0x00 ... 0x00
        K = bytes([0x00] * self.hLen)

        # XXX(caw): these are wrong
        print("int2octets(x)", binascii.hexlify(int2octets(x)))
        print("bits2octets(h1)", binascii.hexlify(bits2octets(h1)))
        
        # d. K = HMAC_K(V || 0x00 || int2octets(x) || bits2octets(h1))
        K = hmac.digest(K, V + bytes([0x00]) + int2octets(x) + bits2octets(h1), self.H)
        # e. V = HMAC_K(V)
        V = hmac.digest(K, V, self.H)
        # f. K = HMAC_K(V || 0x01 || int2octets(x) || bits2octets(h1))
        K = hmac.digest(K, V + bytes([0x01]) + int2octets(x) + bits2octets(h1), self.H)
        # g. V = HMAC_K(V)
        V = hmac.digest(K, V, self.H)

        print("K", binascii.hexlify(K))
        print("V", binascii.hexlify(V))
        
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

# XXX(caw, draft): some places public key is Y, other places it's PK
tests = [{
    "SK": "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721",
    "PK": "0360fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6",
    "alpha": "73616d706c65",
    "H": "02b31973e872d4a097e2cfae9f37af9f9d73428fde74ac537dda93b5f18dbc5842",
    "k": "e92820035a0a8afe132826c6312662b6ea733fc1a0d33737945016de54d02dd8",
    "U": "031490f49d0355ffcdf66e40df788bee93861917ee713acff79be40d20cc91a30a",
    "V": "03701df0228138fa3d16612c0d720389326b3265151bc7ac696ea4d0591cd053e3",
    "pi": "0331d984ca8fece9cbb9a144c0d53df3c4c7a33080c1e02ddb1a96a365394c7888a39dfe7432f119228473f37db3f87ca470c63b0237432a791f18f823c1215e276b7ac0962725ba8daec2bf90c0ccc91a",
    "beta": "21e66dc9747430f17ed9efeda054cf4a264b097b9e8956a1787526ed00dc664b"
}]

if __name__ == "__main__":
    vrf = ECVRFP256()
    for t in tests:
        SK = string_to_int(binascii.unhexlify(t["SK"]))
        PK = vrf.G.deserialize(binascii.unhexlify(t["PK"]))
        alpha_string = binascii.unhexlify(t["alpha"])
        beta_string_expected = binascii.unhexlify(t["beta"])
        pi_string_expected = binascii.unhexlify(t["pi"])

        # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09
        pi_string = vrf.prove(SK, alpha_string)
        beta_string = vrf.proof_to_hash(pi_string)
        valid = vrf.verify(PK, pi_string, alpha_string)
        assert(pi_string == pi_string_expected)
        assert(beta_string == beta_string_expected)
        assert(valid)

        # https://datatracker.ietf.org/doc/html/rfc6979#appendix-A.2.5
        x = string_to_int(binascii.unhexlify("C9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721"))
        expected_k = string_to_int(binascii.unhexlify("A6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60"))
        k = vrf.nonce_generation(x, _as_bytes("sample"))
        assert(k == expected_k)
