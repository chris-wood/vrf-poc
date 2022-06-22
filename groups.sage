#!/usr/bin/sage
# vim: syntax=python

import sys

import random
import hashlib

from hash_to_field import I2OSP, OS2IP, expand_message_xmd, hash_to_field

try:
    from sagelib.suite_p256 import p256_sswu_ro, p256_sswu_nu, p256_order, p256_p, p256_F, p256_A, p256_B
    from sagelib.suite_25519 import edw25519_sha512_nu
    from sagelib.common import sgn0
except ImportError as e:
    sys.exit("Error loading preprocessed sage files. Try running `make setup && make clean pyfiles`. Full error: " + e)

if sys.version_info[0] == 3:
    xrange = range
    _as_bytes = lambda x: x if isinstance(x, bytes) else bytes(x, "utf-8")
    _strxor = lambda str1, str2: bytes( s1 ^ s2 for (s1, s2) in zip(str1, str2) )
else:
    _as_bytes = lambda x: x
    _strxor = lambda str1, str2: ''.join( chr(ord(s1) ^ ord(s2)) for (s1, s2) in zip(str1, str2) )

# Fix a seed so all test vectors are deterministic
FIXED_SEED = "oprf".encode('utf-8')
random.seed(int.from_bytes(hashlib.sha256(FIXED_SEED).digest(), 'big'))

class Group(object):
    def __init__(self, name):
        self.name = name

    def generator(self):
        return None

    def identity(self):
        return 0

    def order(self):
        return 0

    def serialize(self, element):
        return None

    def deserialize(self, encoded):
        return None

    def serialize_scalar(self, scalar):
        pass

    def element_byte_length(self):
        pass

    def scalar_byte_length(self):
        pass

    def hash_to_group(self, x):
        return None

    def hash_to_scalar(self, x):
        return None

    def random_scalar(self):
        return random.randint(1, self.order() - 1)

    def key_gen(self):
        skS = ZZ(self.random_scalar())
        pkS = self.generator() * skS
        return skS, pkS

    def __str__(self):
        return self.name

class GroupNISTCurve(Group):
    def __init__(self, name, suite, F, A, B, p, order, gx, gy, L, H, expand, k):
        Group.__init__(self, name)
        self.F = F
        EC = EllipticCurve(F, [F(A), F(B)])
        self.curve = EC
        self.gx = gx
        self.gy = gy
        self.p = p
        self.a = A
        self.b = B
        self.group_order = order
        self.h2c_suite = suite
        self.G = EC(F(gx), F(gy))
        self.m = F.degree()
        self.L = L
        self.k = k
        self.H = H
        self.expand = expand
        self.field_bytes_length = int(ceil(len(self.p.bits()) / 8))
        self.cofactor = 1

    def generator(self):
        return self.G

    def order(self):
        return self.group_order

    def identity(self):
        return self.curve(0)

    def serialize(self, element):
        x, y = element[0], element[1]
        sgn = sgn0(y)
        byte = 2 if sgn == 0 else 3
        return I2OSP(byte, 1) + I2OSP(x, self.field_bytes_length)

   # this is using point compression
    def deserialize(self, encoded):
        # 0x02 | 0x03 || x
        pve = encoded[0] == 0x02
        nve = encoded[0] == 0x03
        assert(pve or nve)
        assert(len(encoded) % 2 != 0)
        element_length = (len(encoded) - 1) / 2
        x = OS2IP(encoded[1:])
        y2 = x^3 + self.a*x + self.b
        y = y2.sqrt()
        parity = 0 if pve else 1
        if sgn0(y) != parity:
            y = -y
        return self.curve(self.F(x), self.F(y))

    def serialize_scalar(self, scalar):
        return I2OSP(scalar % self.order(), self.scalar_byte_length())

    def element_byte_length(self):
        return int(1 + self.field_bytes_length)

    def scalar_byte_length(self):
        return int(self.field_bytes_length)

    def hash_to_group(self, msg, dst):
        self.h2c_suite.expand._dst = dst
        return self.h2c_suite(msg)

    def hash_to_scalar(self, msg, dst=""):
        return hash_to_field(msg, 1, dst, self.order(), self.m, self.L, self.expand, self.H, self.k)[0][0]

class GroupP256(GroupNISTCurve):
    def __init__(self):
        # See FIPS 186-3, section D.2.3
        gx = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
        gy = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
        GroupNISTCurve.__init__(self, "P256_XMD:SHA-512_SSWU_RO_", p256_sswu_ro, p256_F, p256_A, p256_B, p256_p, p256_order, gx, gy, 48, hashlib.sha256, expand_message_xmd, 128)

class GroupP256NU(GroupNISTCurve):
    def __init__(self):
        # See FIPS 186-3, section D.2.3
        gx = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
        gy = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
        GroupNISTCurve.__init__(self, "P256_XMD:SHA-256_SSWU_NU_", p256_sswu_nu, p256_F, p256_A, p256_B, p256_p, p256_order, gx, gy, 48, hashlib.sha256, expand_message_xmd, 128)

class GroupP384(GroupNISTCurve):
    def __init__(self):
        # See FIPS 186-3, section D.2.4
        gx = 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7
        gy = 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f
        GroupNISTCurve.__init__(self, "P384_XMD:SHA-512_SSWU_RO_", p384_sswu_ro, p384_F, p384_A, p384_B, p384_p, p384_order, gx, gy, 72, hashlib.sha512, expand_message_xmd, 192)

class GroupP521(GroupNISTCurve):
    def __init__(self):
        # See FIPS 186-3, section D.2.5
        gx = 0xc6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66
        gy = 0x11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650
        GroupNISTCurve.__init__(self, "P521_XMD:SHA-512_SSWU_RO_", p521_sswu_ro, p521_F, p521_A, p521_B, p521_p, p521_order, gx, gy, 98, hashlib.sha512, expand_message_xmd, 256)

class GroupEd25519(Group):
    # Compute corresponding x-coordinate, with low bit corresponding to
    # sign, or return None on failure
    def recover_x(y, sign, p, d):
        def modp_inv(x):
            return pow(x, p-2, p)
        if y >= p:
            return None
        x2 = (y^2-1) * modp_inv(d*y^2+1)
        if x2 == 0:
            if sign:
                return None
            else:
                return 0

        # Compute square root of x2
        x = int(pow(x2, (p+3) // 8, p))
        if (x*x - x2) % p != 0:
            modp_sqrt_m1 = pow(2, (p-1) // 4, p)
            x = int(x * modp_sqrt_m1 % p)
        if (x*x - x2) % p != 0:
            return None

        if (x & 1) != sign:
            x = p - x
        return x

    def to_weierstrass(a, d, x, y):
        return ((5*a + a*y - 5*d*y - d)/(12 - 12*y), (a + a*y - d*y -d)/(4*x - 4*x*y))

    def to_twistededwards(a, d, u, v):
        y = (5*a - 12*u - d)/(-12*u - a + 5*d)
        x = (a + a*y - d*y -d)/(4*v - 4*v*y)
        return (x, y)

    def __init__(self):
        Group.__init__(self, "ed25519")
        # Borrowed from: https://neuromancer.sk/std/other/Ed25519
        p = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed
        K = GF(p)
        a = K(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec)
        d = 0x52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3
        E = EllipticCurve(K, (K(-1/48) * (a^2 + 14*a*d + d^2),K(1/864) * (a + d) * (-a^2 + 34*a*d - d^2)))
        G = E(*GroupEd25519.to_weierstrass(a, K(d), K(0x216936D3CD6E53FEC0A4E231FDD6DC5C692CC7609525A7B2C9562D608F25D51A), K(0x6666666666666666666666666666666666666666666666666666666666666658)))
        order = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed * 0x08
        E.set_order(order)

        self.F = K
        self.curve = E
        self.p = p
        self.group_order = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed
        self.G = G
        self.a = a
        self.d = d
        self.field_bytes_length = 32
        self.cofactor = 8

    def generator(self):
        return self.G

    def order(self):
        return self.group_order

    def identity(self):
        return self.curve(0)

    def inner_serialize(self, u, v):
        sign = int(int(u) % 2)
        return int.to_bytes(int(v) | (sign << 255), 32, "little")

    def serialize(self, element):
        (x, y) = element.xy()
        (u, v) = GroupEd25519.to_twistededwards(self.a, self.d, x, y)
        return self.inner_serialize(u, v)

    def deserialize(self, encoded):
        if len(encoded) != 32:
            raise Exception("Invalid input length for decompression")
        y = int.from_bytes(encoded, "little")
        sign = int(y) >> 255
        y = int(int(y) & ((1 << 255) - 1))

        x = GroupEd25519.recover_x(y, sign, self.p, self.d)
        if x is None:
            return None
        else:
            (u, v) = GroupEd25519.to_weierstrass(self.a, self.F(self.d), x, y)
            return self.curve(u, v)

    def serialize_scalar(self, scalar):
        return int.to_bytes(int(scalar) % int(self.group_order), 32, "little")

    def element_byte_length(self):
        return 32

    def scalar_byte_length(self):
        return 32

    def hash_to_group(self, msg, dst):
        suite = edw25519_sha512_nu
        suite.expand._dst = dst
        point = suite(msg)
        enc = self.inner_serialize(point[0], point[1])
        return self.deserialize(enc)

    def hash_to_scalar(self, msg, dst=""):
        # From RFC8032. Note that the DST is ignored.
        return int.from_bytes(hashlib.sha512(msg).digest(), "little") % self.order()
