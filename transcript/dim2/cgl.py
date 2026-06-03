from utilities import sqrt_Fp2, fourth_Fp2, eighth_Fp2


class CGL:
    def __init__(self, domain, chunk=1, block_size=324):
        assert block_size % chunk == 0
        self.domain = domain
        self.chunk = chunk
        self.block_size = block_size

    def __repr__(self):
        return f"CGL with domain = {self.domain}"

    def sqrt(self, x):
        return sqrt_Fp2(x)

    def fourth_root(self, x):
        return fourth_Fp2(x)

    def eighth_root(self, x):
        return eighth_Fp2(x)

    def advance(self, bits=None):
        pass

    def bit_string(self, message):
        r = self
        for x in range(0, len(message), self.chunk):
            bits = message[x : x + self.chunk]
            r = r.advance(bits)
        return r
    
    def pad_msg(self, msg):
        length_slot = 64
        assert self.block_size > length_slot

        length = len(msg)

        # Append the '1' at the most most significant bit:
        msg.append(1)

        # Pad with '0' bytes until the message's length in bits is block_size:
        r = len(msg) % self.block_size
        available = self.block_size - length_slot
        if r <= available:
            pad_len = available - r
        else:
            pad_len = 2 * self.block_size - r - length_slot
        pad = [0] * pad_len
        msg += pad

        length_bits = [int(bit) for bit in bin(length)[2:]]
        l = len(length_bits)
        length_bits = [0] * (length_slot - l) + length_bits
        msg += length_bits

        assert len(msg) % self.block_size == 0
        return msg

    def to_hash():
        pass

    def hash(self, bits):
        # Pad the message
        bits = self.pad_msg(bits[:])

        # Compute the CGL hash
        r = self.bit_string(bits)
        return r.to_hash()
