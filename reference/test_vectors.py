#!/usr/bin/env python3
"""
Mambo Cryptographic Primitive — Official Test Vectors
=====================================================

Map with round constants:
    theta' = (phi * theta + psi^2 + c_i) mod p
    psi'   = (phi * psi + theta'^2 + d_i) mod p

Output extraction: XOR(theta, psi)

Round constants derived from SHA-256 in counter mode:
    h_j = SHA-256("Mambo_round_constants" || BE32(j))
    c_i = int(h_i) mod p,      i in [0..63]
    d_i = int(h_{64+i}) mod p, i in [0..63]
    Zero values replaced with 1.
"""

import hashlib
import struct


# ---------------------------------------------------------------------------
# Round constant generation
# ---------------------------------------------------------------------------

def generate_round_constants(n_rounds, p, seed=b'Mambo_round_constants'):
    """
    Generate 2*n_rounds constants from SHA-256 counter mode.

    Returns (rc_c, rc_d) where each is a list of n_rounds field elements.
    Derivation:
        For j in [0, 2*n_rounds):
            h = SHA-256(seed || BE32(j))
            val = int.from_bytes(h, 'big') % p
            if val == 0: val = 1
        rc_c = vals[0:n_rounds]
        rc_d = vals[n_rounds:2*n_rounds]
    """
    vals = []
    for j in range(n_rounds * 2):
        h = hashlib.sha256(seed + j.to_bytes(4, 'big')).digest()
        v = int.from_bytes(h, 'big') % p
        vals.append(v if v != 0 else 1)
    return vals[:n_rounds], vals[n_rounds:]


# ---------------------------------------------------------------------------
# Core map
# ---------------------------------------------------------------------------

# Recommended t=2 L1 cell under the conservative cost model:
# D_eff = 2^{t(n-1)-max(t-2,0)} = 2^{2(n-1)} >= 2^128  =>  n = 65.
N_ROUNDS = 65


def mambo_step(theta, psi, phi, p, c=0, d=0):
    """One step of the Mambo map with round constants."""
    theta_new = (phi * theta + psi * psi + c) % p
    psi_new = (phi * psi + theta_new * theta_new + d) % p
    return theta_new, psi_new


def mambo_xor_output(theta, psi):
    """XOR extraction."""
    return theta ^ psi


def compute_vectors(name, p, phi, theta0, psi0, steps=20):
    """Compute and print test vectors with round constants."""
    rc_c, rc_d = generate_round_constants(N_ROUNDS, p)

    # Determine hex width based on p
    hex_width = (p.bit_length() + 3) // 4

    print(f"\n{'=' * 120}")
    print(f"  {name}")
    print(f"{'=' * 120}")
    print(f"  p   = {p}")
    print(f"      = 0x{p:0{hex_width}x}")
    print(f"  phi = {phi}")
    print(f"      = 0x{phi:0{hex_width}x}")
    print(f"  Seed: theta_0 = {theta0}, psi_0 = {psi0}")
    print(f"  Round constants: SHA-256 counter mode, seed='Mambo_round_constants'")
    print(f"  First c_0 = {rc_c[0]}")
    print(f"  First d_0 = {rc_d[0]}")
    print(f"{'=' * 120}")
    print()

    # Header
    step_w = 4
    hex_col = hex_width + 2
    print(f"{'step':>{step_w}} | {'theta (hex)':>{hex_col}} | {'psi (hex)':>{hex_col}} | {'xor_output (hex)':>{hex_col}}")
    print(f"{'-' * step_w}-+-{'-' * hex_col}-+-{'-' * hex_col}-+-{'-' * hex_col}")

    # Step 0: initial state
    theta, psi = theta0, psi0
    xor_out = mambo_xor_output(theta, psi)
    print(f"{0:>{step_w}} | 0x{theta:0{hex_width}x} | 0x{psi:0{hex_width}x} | 0x{xor_out:0{hex_width}x}")

    # Steps 1..steps (with round constants)
    for i in range(1, steps + 1):
        ci = rc_c[(i - 1) % N_ROUNDS]
        di = rc_d[(i - 1) % N_ROUNDS]
        theta, psi = mambo_step(theta, psi, phi, p, ci, di)
        xor_out = mambo_xor_output(theta, psi)
        print(f"{i:>{step_w}} | 0x{theta:0{hex_width}x} | 0x{psi:0{hex_width}x} | 0x{xor_out:0{hex_width}x}")

    return theta, psi


def mambo_hash_md(message_blocks, p, phi, iv_theta=0, iv_psi=0, rounds_per_block=65):
    """
    Merkle-Damgard hash using Mambo as the compression function.

    Each message block m_i is injected as:
        theta = (theta + m_i) mod p
    Then `rounds_per_block` steps of the Mambo map are applied
    with round constants cycling modulo 64.

    Output: XOR(theta_final, psi_final), truncated/formatted as needed.
    """
    rc_c, rc_d = generate_round_constants(N_ROUNDS, p)
    theta, psi = iv_theta, iv_psi
    for block in message_blocks:
        theta = (theta + block) % p
        for r in range(rounds_per_block):
            ci = rc_c[r % N_ROUNDS]
            di = rc_d[r % N_ROUNDS]
            theta, psi = mambo_step(theta, psi, phi, p, ci, di)
    return theta, psi, mambo_xor_output(theta, psi)


def compute_hash_vectors(name, p, phi, hex_width):
    """Compute hash test vectors using Merkle-Damgard construction."""
    print(f"\n{'=' * 120}")
    print(f"  Mambo-Hash (Merkle-Damgard) — {name}")
    print(f"{'=' * 120}")
    print(f"  Construction: Merkle-Damgard with message injection into theta")
    print(f"  Compression: theta = (theta + m_i) mod p, then 65 Mambo steps with round constants")
    print(f"  IV: theta_0 = 0, psi_0 = 0")
    print(f"  Output: XOR(theta_final, psi_final)")
    print(f"{'=' * 120}")
    print()

    # Test vector 1: single block, m = [1]
    msg1 = [1]
    t1, p1, h1 = mambo_hash_md(msg1, p, phi, iv_theta=0, iv_psi=0, rounds_per_block=65)
    print(f"  Message: [1]  (single block)")
    print(f"    theta_final = 0x{t1:0{hex_width}x}")
    print(f"    psi_final   = 0x{p1:0{hex_width}x}")
    print(f"    hash        = 0x{h1:0{hex_width}x}")
    print()

    # Test vector 2: single block, m = [2]
    msg2 = [2]
    t2, p2, h2 = mambo_hash_md(msg2, p, phi, iv_theta=0, iv_psi=0, rounds_per_block=65)
    print(f"  Message: [2]  (single block)")
    print(f"    theta_final = 0x{t2:0{hex_width}x}")
    print(f"    psi_final   = 0x{p2:0{hex_width}x}")
    print(f"    hash        = 0x{h2:0{hex_width}x}")
    print()

    # Test vector 3: two blocks, m = [1, 2]
    msg3 = [1, 2]
    t3, p3, h3 = mambo_hash_md(msg3, p, phi, iv_theta=0, iv_psi=0, rounds_per_block=65)
    print(f"  Message: [1, 2]  (two blocks)")
    print(f"    theta_final = 0x{t3:0{hex_width}x}")
    print(f"    psi_final   = 0x{p3:0{hex_width}x}")
    print(f"    hash        = 0x{h3:0{hex_width}x}")
    print()

    # Test vector 4: "Hello" as ASCII blocks
    hello = [ord(c) for c in "Hello"]
    t4, p4, h4 = mambo_hash_md(hello, p, phi, iv_theta=0, iv_psi=0, rounds_per_block=65)
    print(f"  Message: \"Hello\" = {hello}  (5 blocks, ASCII)")
    print(f"    theta_final = 0x{t4:0{hex_width}x}")
    print(f"    psi_final   = 0x{p4:0{hex_width}x}")
    print(f"    hash        = 0x{h4:0{hex_width}x}")
    print()

    # Avalanche: "Hello" vs "Hellp" — 1-bit difference
    hellp = [ord(c) for c in "Hellp"]
    t5, p5, h5 = mambo_hash_md(hellp, p, phi, iv_theta=0, iv_psi=0, rounds_per_block=65)
    hamming = bin(h4 ^ h5).count('1')
    total_bits = p.bit_length()
    print(f"  Message: \"Hellp\" = {hellp}  (avalanche test: 'o'→'p', 1-bit input diff)")
    print(f"    theta_final = 0x{t5:0{hex_width}x}")
    print(f"    psi_final   = 0x{p5:0{hex_width}x}")
    print(f"    hash        = 0x{h5:0{hex_width}x}")
    print(f"    Avalanche: Hamming distance = {hamming}/{total_bits} bits ({100*hamming/total_bits:.1f}%)")
    print()


def main():
    print("=" * 120)
    print("  MAMBO CRYPTOGRAPHIC PRIMITIVE — OFFICIAL TEST VECTORS")
    print("  Map: theta' = (phi * theta + psi^2 + c_i) mod p")
    print("       psi'   = (phi * psi + theta'^2 + d_i) mod p")
    print("  Output: XOR(theta, psi)")
    print("  Round constants: SHA-256('Mambo_round_constants' || BE32(j))")
    print("=" * 120)

    # ---------------------------------------------------------------
    # Configuration 1: Mersenne prime  p = 2^61 - 1
    # ---------------------------------------------------------------
    p_mersenne = (1 << 61) - 1
    phi_mersenne = 1975947453787198142
    assert p_mersenne == 2305843009213693951
    compute_vectors(
        "Configuration 1: Mersenne Prime  p = 2^61 - 1",
        p_mersenne, phi_mersenne, 1, 1, steps=20
    )

    # ---------------------------------------------------------------
    # Configuration 2: Goldilocks prime  p = 2^64 - 2^32 + 1
    # ---------------------------------------------------------------
    p_goldilocks = (1 << 64) - (1 << 32) + 1
    phi_goldilocks = 16032412539219608744
    assert p_goldilocks == 18446744069414584321
    compute_vectors(
        "Configuration 2: Goldilocks Prime  p = 2^64 - 2^32 + 1",
        p_goldilocks, phi_goldilocks, 1, 1, steps=20
    )

    # ---------------------------------------------------------------
    # Configuration 3: BN254 scalar field
    # ---------------------------------------------------------------
    p_bn254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    phi_bn254 = 7
    compute_vectors(
        "Configuration 3: BN254 Scalar Field  (phi = 7)",
        p_bn254, phi_bn254, 1, 1, steps=20
    )

    # ---------------------------------------------------------------
    # Hash test vectors (Merkle-Damgard with round constants)
    # ---------------------------------------------------------------
    hw_mersenne = (p_mersenne.bit_length() + 3) // 4
    hw_goldilocks = (p_goldilocks.bit_length() + 3) // 4
    hw_bn254 = (p_bn254.bit_length() + 3) // 4

    compute_hash_vectors("Mersenne (2^61-1)", p_mersenne, phi_mersenne, hw_mersenne)
    compute_hash_vectors("Goldilocks (2^64-2^32+1)", p_goldilocks, phi_goldilocks, hw_goldilocks)
    compute_hash_vectors("BN254", p_bn254, phi_bn254, hw_bn254)

    print("\n" + "=" * 120)
    print("  END OF TEST VECTORS")
    print("=" * 120)


if __name__ == "__main__":
    main()
