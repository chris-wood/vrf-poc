#!/usr/bin/sage
# vim: syntax=python

import sys
import hashlib
import hmac
import binascii
import struct

from hash_to_field import I2OSP, OS2IP
from ed25519_rfc8032 import secret_expand, sha512_modq

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
    from sagelib.groups import GroupP256NU, GroupEd25519
except ImportError:
    sys.exit("Error loading preprocessed sage files. Try running `make clean pyfiles`")

# little-endian version of I2OSP
def I2OSP_le(val, length):
    val = int(val)
    if val < 0 or val >= (1 << (8 * length)):
        raise ValueError("bad I2OSP call: val=%d length=%d" % (val, length))
    ret = [0] * length
    val_ = val
    for idx in range(0, length):
        ret[idx] = val_ & 0xff
        val_ = val_ >> 8
    ret = struct.pack("=" + "B" * length, *ret)
    assert OS2IP_le(ret, True) == val
    return ret

# little-endian version of OS2IP
def OS2IP_le(octets, skip_assert=False):
    ret = 0
    for octet in reversed(struct.unpack("=" + "B" * len(octets), octets)):
        ret = ret << 8
        ret += octet
    if not skip_assert:
        assert octets == I2OSP_le(ret, len(octets))
    return ret

class ECVRF(object):
    def __init__(self, G, H, suite_string, h2c_suite):
        self.G = G
        self.H = H
        self.ptLen = G.element_byte_length()
        self.qLen = ceil(log(G.order(), 2) / 8)
        self.hLen = H().digest_size
        self.suite_string = suite_string
        self.h2c_suite_ID_string = h2c_suite
        self.cofactor = G.cofactor

    def int_to_string(self, i, n):
        return I2OSP(i, n)

    def string_to_int(self, s):
        return OS2IP(s)

    def point_to_string(self, x):
        return self.G.serialize(x)

    def string_to_point(self, p):
        return self.G.deserialize(p)

    def derive_scalar_from_SK(self, SK):
        raise Exception("to implement")

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.1
    def prove(self, SK, alpha_string):
        x = self.derive_scalar_from_SK(SK)
        cLen = self.cLen
        qLen = self.qLen
        B = self.G.generator()

        Y = x * B
        PK_string = self.point_to_string(Y)
        H = self.encode_to_curve(PK_string, alpha_string)
        h_string = self.point_to_string(H)
        Gamma = x * H
        k = self.nonce_generation(SK, h_string)
        c = self.challenge_generation([Y, H, Gamma, k * B, k * H])
        s = (k + (c * x)) % self.G.order()
        pi_string = self.point_to_string(Gamma) + self.int_to_string(c, cLen) + self.int_to_string(s, qLen)

        return pi_string

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.2
    def proof_to_hash(self, pi_string):
        (Gamma, _, s) = self.decode_proof(pi_string)
        three_string = self.int_to_string(3, 1)
        zero_string = self.int_to_string(0, 1)

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
        PK_string = self.point_to_string(Y)
        H = self.encode_to_curve(PK_string, alpha_string)
        U = (s * B) - (c * Y)
        V = (s * H) - (c * Gamma)
        c_prime = self.challenge_generation([Y, H, Gamma, U, V])
        return c == c_prime

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.4.1.2
    def encode_to_curve(self, encode_to_curve_salt, alpha_string):
        string_to_hash = encode_to_curve_salt + alpha_string
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
    def challenge_generation(self, points):
        two_string = self.int_to_string(2, 1)
        hash_str = self.suite_string + two_string
        for p_j in points:
            hash_str = hash_str + self.point_to_string(p_j)
        zero_string = self.int_to_string(0, 1)
        hash_str = hash_str + zero_string

        hasher = self.H()
        hasher.update(hash_str)
        c_string = hasher.digest()
        truncated_c_string = c_string[0:self.cLen]
        c = self.string_to_int(truncated_c_string)
        return c

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.4.4
    def decode_proof(self, pi_string):
        gamma_string = pi_string[0:self.ptLen]
        c_string = pi_string[self.ptLen:self.ptLen+self.cLen]
        s_string = pi_string[self.ptLen+self.cLen:self.ptLen+self.cLen+self.qLen]
        Gamma = self.string_to_point(gamma_string)
        c = self.string_to_int(c_string)
        s = self.string_to_int(s_string)
        return (Gamma, c, s)

# ECVRF-P256-SHA256-SSWU, P256_XMD:SHA-256_SSWU_NU_
class ECVRFP256(ECVRF):
    def __init__(self):
        ECVRF.__init__(self, GroupP256NU(), hashlib.sha256, self.int_to_string(2, 1), _as_bytes("P256_XMD:SHA-256_SSWU_NU_"))
        self.cLen = 16

    def derive_scalar_from_SK(self, SK):
        return self.string_to_int(SK)

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.4.2.1 for p256
    def nonce_generation(self, SK, h_string):
        m = h_string
        x = self.derive_scalar_from_SK(SK)
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
            return self.int_to_string(m, self.qLen)
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
        ECVRF.__init__(self, GroupEd25519(), hashlib.sha512, self.int_to_string(4, 1), _as_bytes("edwards25519_XMD:SHA-512_ELL2_NU_"))
        self.cLen = 16
    
    def int_to_string(self, i, n):
        return I2OSP_le(i, n)

    def string_to_int(self, s):
        return OS2IP_le(s)

    def derive_scalar_from_SK(self, SK):
        return int(secret_expand(SK)[0])

    # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-09#section-5.4.2.2
    def nonce_generation(self, SK, h_string):
        # 1.  hashed_sk_string = Hash(SK)
        # 2.  truncated_hashed_sk_string = hashed_sk_string[32]...hashed_sk_string[63]
        truncated_hashed_sk_string = secret_expand(SK)[1]

        # 3.  k_string = Hash(truncated_hashed_sk_string || h_string)
        # 4.  k = string_to_int(k_string) mod q
        k = sha512_modq(truncated_hashed_sk_string + h_string)

        return k

vrf_vectors = [
    {
        # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-13#appendix-A.2
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
                "pi": "0331d984ca8fece9cbb9a144c0d53df3c4c7a33080c1e02ddb1a96a365394c7888782fffde7b842c38c20c08de6ec6c2e7027a97000f2c9fa4425d5c03e639fb48fde58114d755985498d7eb234cf4aed9",
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
                "pi": "03f814c0455d32dbc75ad3aea08c7e2db31748e12802db23640203aebf1fa8db2743aad348a3006dc1caad7da28687320740bf7dd78fe13c298867321ce3b36b79ec3093b7083ac5e4daf3465f9f43c627",
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
                "pi": "039f8d9cdc162c89be2871cbcb1435144739431db7fab437ab7bc4e2651a9e99d5488405a11a6c7fc8defddd9e1573a563b7333aab4effe73ae9803274174c659269fd39b53e133dcd9e0d24f01288de9a",
                "beta": "4fbadf33b42a5f42f23a6f89952d2e634a6e3810f15878b46ef1bb85a04fe95a",
            }
        ]
    },
    {
        # https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-13#appendix-A.4
        "vrf": ECVRFEd25519,
        "tests": [
            {
                "SK": "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
                "PK": "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
                "alpha": "",
                "H": "b8066ebbb706c72b64390324e4a3276f129569eab100c26b9f05011200c1bad9",
                "k": "55cbb247af9b8372259a97b2cfec656d78868deb33b203d51b9961c364522400",
                "U": "762f5c178b68f0cddcc1157918edf45ec334ac8e8286601a3256c3bbf858edd9",
                "V": "4652eba1c4612e6fce762977a59420b451e12964adbe4fbecd58a7aeff5860af",
                "pi": "7d9c633ffeee27349264cf5c667579fc583b4bda63ab71d001f89c10003ab46f14adf9a3cd8b8412d9038531e865c341cafa73589b023d14311c331a9ad15ff2fb37831e00f0acaa6d73bc9997b06501",
                "beta": "9d574bf9b8302ec0fc1e21c3ec5368269527b87b462ce36dab2d14ccf80c53cccf6758f058c5b1c856b116388152bbe509ee3b9ecfe63d93c3b4346c1fbc6c54"
            },
            {
                "SK": "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
                "PK": "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
                "alpha": "72",
                "H": "76ac3ccb86158a9104dff819b1ca293426d305fd76b39b13c9356d9b58c08e57",
                "k": "9565956daeedf376cad61b829b2a4d21ba1b52e9b3e2457477a64630a9711003",
                "U": "8ec26e77b8cb3114dd2265fe1564a4efb40d109aa3312536d93dfe3d8d80a061",
                "V": "fe799eb5770b4e3a5a27d22518bb631db183c8316bb552155f442c62a47d1c8b",
                "pi": "47b327393ff2dd81336f8a2ef10339112401253b3c714eeda879f12c509072ef055b48372bb82efbdce8e10c8cb9a2f9d60e93908f93df1623ad78a86a028d6bc064dbfc75a6a57379ef855dc6733801",
                "beta": "38561d6b77b71d30eb97a062168ae12b667ce5c28caccdf76bc88e093e4635987cd96814ce55b4689b3dd2947f80e59aac7b7675f8083865b46c89b2ce9cc735"
            },
            {
                "SK": "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
                "PK": "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025",
                "alpha": "af82",
                "H": "13d2a8b5ca32db7e98094a61f656a08c6c964344e058879a386a947a4e189ed1",
                "k": "1fda4077f737098b3f361c33a36cccafd7e9e9b720e1f84011254e25f37eed02",
                "U": "a012f35433df219a88ab0f9481f4e0065d00422c3285f3d34a8b0202f20bac60",
                "V": "fb613986d171b3e98319c7ca4dc44c5dd8314a6e5616c1a4f16ce72bd7a0c25a",
                "pi": "926e895d308f5e328e7aa159c06eddbe56d06846abf5d98c2512235eaa57fdce35b46edfc655bc828d44ad09d1150f31374e7ef73027e14760d42e77341fe05467bb286cc2c9d7fde29120a0b2320d04",
                "beta": "121b7f9b9aaaa29099fc04a94ba52784d44eac976dd1a3cca458733be5cd090a7b5fbd148444f17f8daf1fb55cb04b1ae85a626e30a54b4b0f8abf4a43314a58"
            }
        ]
    }
]

if __name__ == "__main__":
    for vector in vrf_vectors:
        for t in vector["tests"]:
            vrf = vector["vrf"]()
            SK = binascii.unhexlify(t["SK"])
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
