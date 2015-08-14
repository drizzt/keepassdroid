/*
 * Serpent reversed implementation (NESSIE format)
 * Based on Serpent.java, part of GNU Classpath.
 */

package org.bouncycastle.crypto.engines;

import org.bouncycastle.crypto.BlockCipher;
import org.bouncycastle.crypto.CipherParameters;
import org.bouncycastle.crypto.DataLengthException;
import org.bouncycastle.crypto.params.KeyParameter;

/**
 * Serpent is a 32-round substitution-permutation network block cipher,
 * operating on 128-bit blocks and accepting keys of 128, 192, and 256 bits in
 * length. At each round the plaintext is XORed with a 128 bit portion of the
 * session key -- a 4224 bit key computed from the input key -- then one of
 * eight S-boxes are applied, and finally a simple linear transformation is
 * done. Decryption does the exact same thing in reverse order, and using the
 * eight inverses of the S-boxes.
 * <p>
 * Serpent was designed by Ross Anderson, Eli Biham, and Lars Knudsen as a
 * proposed cipher for the Advanced Encryption Standard.
 * <p>
 * Serpent can be sped up greatly by replacing S-box substitution with a
 * sequence of binary operations, and the optimal implementation depends upon
 * finding the fastest sequence of binary operations that reproduce this
 * substitution. This implementation uses the S-boxes discovered by <a
 * href="http://www.ii.uib.no/~osvik/">Dag Arne Osvik</a>, which are optimized
 * for the Pentium family of processors.
 * <p>
 * References:
 * <ol>
 * <li><a href="http://www.cl.cam.ac.uk/~rja14/serpent.html">Serpent: A
 * Candidate Block Cipher for the Advanced Encryption Standard.</a></li>
 * </ol>
 */
public class TnepresEngine
  implements BlockCipher
{
  private static final int    BLOCK_SIZE = 16;

  static final int ROUNDS = 32;
  static final int PHI    = 0x9E3779B9;       // (sqrt(5) - 1) * 2**31

  private boolean        encrypting;
  private int[]          wKey;

  private int           x0, x1, x2, x3, x4;    // registers

  /**
   * initialise a Serpent cipher.
   *
   * @param encrypting whether or not we are for encryption.
   * @param params the parameters required to set up the cipher.
   * @exception IllegalArgumentException if the params argument is
   * inappropriate.
   */
  public void init(
      boolean             encrypting,
      CipherParameters    params)
  {
    if (params instanceof KeyParameter)
    {
      this.encrypting = encrypting;
      this.wKey = makeWorkingKey(((KeyParameter)params).getKey());
      return;
    }

    throw new IllegalArgumentException("invalid parameter passed to Serpent init - " + params.getClass().getName());
  }

  public String getAlgorithmName()
  {
    return "Serpent";
  }

  public int getBlockSize()
  {
    return BLOCK_SIZE;
  }

  /**
   * Process one block of input from the array in and write it to
   * the out array.
   *
   * @param in the array containing the input data.
   * @param inOff offset into the in array the data starts at.
   * @param out the array the output data will be copied into.
   * @param outOff the offset into the out array the output will start at.
   * @exception DataLengthException if there isn't enough data in in, or
   * space in out.
   * @exception IllegalStateException if the cipher isn't initialised.
   * @return the number of bytes processed and produced.
   */
  public final int processBlock(
      byte[]  in,
      int     inOff,
      byte[]  out,
      int     outOff)
  {
    if (wKey == null)
    {
      throw new IllegalStateException("Serpent not initialised");
    }

    if ((inOff + BLOCK_SIZE) > in.length)
    {
      throw new DataLengthException("input buffer too short");
    }

    if ((outOff + BLOCK_SIZE) > out.length)
    {
      throw new DataLengthException("output buffer too short");
    }

    if (encrypting)
    {
      encryptBlock(in, inOff, out, outOff);
    }
    else
    {
      decryptBlock(in, inOff, out, outOff);
    }

    return BLOCK_SIZE;
  }

  public void reset()
  {
  }

  /**
   * Expand a user-supplied key material into a session key.
   *
   * @param key  The user-key bytes (multiples of 4) to use.
   * @exception IllegalArgumentException
   */
  private int[] makeWorkingKey(
      byte[] kb)
    throws  IllegalArgumentException
  {
    // Not strictly true, but here to conform with the AES proposal.
    // This restriction can be removed if deemed necessary.
    if (kb.length != 16 && kb.length != 24 && kb.length != 32)
      throw new IllegalArgumentException("Key length is not 16, 24, or 32 bytes");
    // Here w is our "pre-key".
    int[] w = new int[4 * (ROUNDS + 1)];
    int i, j;
    for (i = 0, j = 0; i < 8 && j < kb.length; i++)
      w[i] = (kb[j++] & 0xff)
        | (kb[j++] & 0xff) << 8
        | (kb[j++] & 0xff) << 16
        | (kb[j++] & 0xff) << 24;
    // Pad key if < 256 bits.
    if (i != 8)
      w[i] = 1;
    // Transform using w_i-8 ... w_i-1
    for (i = 8, j = 0; i < 16; i++)
    {
      int t = w[j] ^ w[i - 5] ^ w[i - 3] ^ w[i - 1] ^ PHI ^ j++;
      w[i] = t << 11 | t >>> 21;
    }
    // Translate by 8.
    for (i = 0; i < 8; i++)
      w[i] = w[i + 8];
    // Transform the rest of the key.
    for (; i < w.length; i++)
    {
      int t = w[i - 8] ^ w[i - 5] ^ w[i - 3] ^ w[i - 1] ^ PHI ^ i;
      w[i] = t << 11 | t >>> 21;
    }
    // After these s-boxes the pre-key (w, above) will become the
    // session key (key, below).
    sbox3(w[0], w[1], w[2], w[3]);
    w[0] = x0;
    w[1] = x1;
    w[2] = x2;
    w[3] = x3;
    sbox2(w[4], w[5], w[6], w[7]);
    w[4] = x0;
    w[5] = x1;
    w[6] = x2;
    w[7] = x3;
    sbox1(w[8], w[9], w[10], w[11]);
    w[8] = x0;
    w[9] = x1;
    w[10] = x2;
    w[11] = x3;
    sbox0(w[12], w[13], w[14], w[15]);
    w[12] = x0;
    w[13] = x1;
    w[14] = x2;
    w[15] = x3;
    sbox7(w[16], w[17], w[18], w[19]);
    w[16] = x0;
    w[17] = x1;
    w[18] = x2;
    w[19] = x3;
    sbox6(w[20], w[21], w[22], w[23]);
    w[20] = x0;
    w[21] = x1;
    w[22] = x2;
    w[23] = x3;
    sbox5(w[24], w[25], w[26], w[27]);
    w[24] = x0;
    w[25] = x1;
    w[26] = x2;
    w[27] = x3;
    sbox4(w[28], w[29], w[30], w[31]);
    w[28] = x0;
    w[29] = x1;
    w[30] = x2;
    w[31] = x3;
    sbox3(w[32], w[33], w[34], w[35]);
    w[32] = x0;
    w[33] = x1;
    w[34] = x2;
    w[35] = x3;
    sbox2(w[36], w[37], w[38], w[39]);
    w[36] = x0;
    w[37] = x1;
    w[38] = x2;
    w[39] = x3;
    sbox1(w[40], w[41], w[42], w[43]);
    w[40] = x0;
    w[41] = x1;
    w[42] = x2;
    w[43] = x3;
    sbox0(w[44], w[45], w[46], w[47]);
    w[44] = x0;
    w[45] = x1;
    w[46] = x2;
    w[47] = x3;
    sbox7(w[48], w[49], w[50], w[51]);
    w[48] = x0;
    w[49] = x1;
    w[50] = x2;
    w[51] = x3;
    sbox6(w[52], w[53], w[54], w[55]);
    w[52] = x0;
    w[53] = x1;
    w[54] = x2;
    w[55] = x3;
    sbox5(w[56], w[57], w[58], w[59]);
    w[56] = x0;
    w[57] = x1;
    w[58] = x2;
    w[59] = x3;
    sbox4(w[60], w[61], w[62], w[63]);
    w[60] = x0;
    w[61] = x1;
    w[62] = x2;
    w[63] = x3;
    sbox3(w[64], w[65], w[66], w[67]);
    w[64] = x0;
    w[65] = x1;
    w[66] = x2;
    w[67] = x3;
    sbox2(w[68], w[69], w[70], w[71]);
    w[68] = x0;
    w[69] = x1;
    w[70] = x2;
    w[71] = x3;
    sbox1(w[72], w[73], w[74], w[75]);
    w[72] = x0;
    w[73] = x1;
    w[74] = x2;
    w[75] = x3;
    sbox0(w[76], w[77], w[78], w[79]);
    w[76] = x0;
    w[77] = x1;
    w[78] = x2;
    w[79] = x3;
    sbox7(w[80], w[81], w[82], w[83]);
    w[80] = x0;
    w[81] = x1;
    w[82] = x2;
    w[83] = x3;
    sbox6(w[84], w[85], w[86], w[87]);
    w[84] = x0;
    w[85] = x1;
    w[86] = x2;
    w[87] = x3;
    sbox5(w[88], w[89], w[90], w[91]);
    w[88] = x0;
    w[89] = x1;
    w[90] = x2;
    w[91] = x3;
    sbox4(w[92], w[93], w[94], w[95]);
    w[92] = x0;
    w[93] = x1;
    w[94] = x2;
    w[95] = x3;
    sbox3(w[96], w[97], w[98], w[99]);
    w[96] = x0;
    w[97] = x1;
    w[98] = x2;
    w[99] = x3;
    sbox2(w[100], w[101], w[102], w[103]);
    w[100] = x0;
    w[101] = x1;
    w[102] = x2;
    w[103] = x3;
    sbox1(w[104], w[105], w[106], w[107]);
    w[104] = x0;
    w[105] = x1;
    w[106] = x2;
    w[107] = x3;
    sbox0(w[108], w[109], w[110], w[111]);
    w[108] = x0;
    w[109] = x1;
    w[110] = x2;
    w[111] = x3;
    sbox7(w[112], w[113], w[114], w[115]);
    w[112] = x0;
    w[113] = x1;
    w[114] = x2;
    w[115] = x3;
    sbox6(w[116], w[117], w[118], w[119]);
    w[116] = x0;
    w[117] = x1;
    w[118] = x2;
    w[119] = x3;
    sbox5(w[120], w[121], w[122], w[123]);
    w[120] = x0;
    w[121] = x1;
    w[122] = x2;
    w[123] = x3;
    sbox4(w[124], w[125], w[126], w[127]);
    w[124] = x0;
    w[125] = x1;
    w[126] = x2;
    w[127] = x3;
    sbox3(w[128], w[129], w[130], w[131]);
    w[128] = x0;
    w[129] = x1;
    w[130] = x2;
    w[131] = x3;
    return w;
  }

  /**
   * Encrypt one block of plaintext.
   *
   * @param in the array containing the input data.
   * @param i offset into the in array the data starts at.
   * @param out the array the output data will be copied into.
   * @param o the offset into the out array the output will start at.
   */
  private void encryptBlock(
      byte[]  in,
      int     i,
      byte[]  out,
      int     o)
  {
    x0 = (in[i     ] & 0xff)
      | (in[i +  1] & 0xff) << 8
      | (in[i +  2] & 0xff) << 16
      | (in[i +  3] & 0xff) << 24;
    x1 = (in[i +  4] & 0xff)
      | (in[i +  5] & 0xff) << 8
      | (in[i +  6] & 0xff) << 16
      | (in[i +  7] & 0xff) << 24;
    x2 = (in[i +  8] & 0xff)
      | (in[i +  9] & 0xff) << 8
      | (in[i + 10] & 0xff) << 16
      | (in[i + 11] & 0xff) << 24;
    x3 = (in[i + 12] & 0xff)
      | (in[i + 13] & 0xff) << 8
      | (in[i + 14] & 0xff) << 16
      | (in[i + 15] & 0xff) << 24;
    x0 ^= wKey[0];
    x1 ^= wKey[1];
    x2 ^= wKey[2];
    x3 ^= wKey[3];
    sbox0();
    x1 ^= wKey[4];
    x4 ^= wKey[5];
    x2 ^= wKey[6];
    x0 ^= wKey[7];
    sbox1();
    x0 ^= wKey[8];
    x4 ^= wKey[9];
    x2 ^= wKey[10];
    x1 ^= wKey[11];
    sbox2();
    x2 ^= wKey[12];
    x1 ^= wKey[13];
    x4 ^= wKey[14];
    x3 ^= wKey[15];
    sbox3();
    x1 ^= wKey[16];
    x4 ^= wKey[17];
    x3 ^= wKey[18];
    x0 ^= wKey[19];
    sbox4();
    x4 ^= wKey[20];
    x2 ^= wKey[21];
    x1 ^= wKey[22];
    x0 ^= wKey[23];
    sbox5();
    x2 ^= wKey[24];
    x0 ^= wKey[25];
    x4 ^= wKey[26];
    x1 ^= wKey[27];
    sbox6();
    x2 ^= wKey[28];
    x0 ^= wKey[29];
    x3 ^= wKey[30];
    x4 ^= wKey[31];
    sbox7();
    x0 = x3;
    x3 = x2;
    x2 = x4;
    x0 ^= wKey[32];
    x1 ^= wKey[33];
    x2 ^= wKey[34];
    x3 ^= wKey[35];
    sbox0();
    x1 ^= wKey[36];
    x4 ^= wKey[37];
    x2 ^= wKey[38];
    x0 ^= wKey[39];
    sbox1();
    x0 ^= wKey[40];
    x4 ^= wKey[41];
    x2 ^= wKey[42];
    x1 ^= wKey[43];
    sbox2();
    x2 ^= wKey[44];
    x1 ^= wKey[45];
    x4 ^= wKey[46];
    x3 ^= wKey[47];
    sbox3();
    x1 ^= wKey[48];
    x4 ^= wKey[49];
    x3 ^= wKey[50];
    x0 ^= wKey[51];
    sbox4();
    x4 ^= wKey[52];
    x2 ^= wKey[53];
    x1 ^= wKey[54];
    x0 ^= wKey[55];
    sbox5();
    x2 ^= wKey[56];
    x0 ^= wKey[57];
    x4 ^= wKey[58];
    x1 ^= wKey[59];
    sbox6();
    x2 ^= wKey[60];
    x0 ^= wKey[61];
    x3 ^= wKey[62];
    x4 ^= wKey[63];
    sbox7();
    x0 = x3;
    x3 = x2;
    x2 = x4;
    x0 ^= wKey[64];
    x1 ^= wKey[65];
    x2 ^= wKey[66];
    x3 ^= wKey[67];
    sbox0();
    x1 ^= wKey[68];
    x4 ^= wKey[69];
    x2 ^= wKey[70];
    x0 ^= wKey[71];
    sbox1();
    x0 ^= wKey[72];
    x4 ^= wKey[73];
    x2 ^= wKey[74];
    x1 ^= wKey[75];
    sbox2();
    x2 ^= wKey[76];
    x1 ^= wKey[77];
    x4 ^= wKey[78];
    x3 ^= wKey[79];
    sbox3();
    x1 ^= wKey[80];
    x4 ^= wKey[81];
    x3 ^= wKey[82];
    x0 ^= wKey[83];
    sbox4();
    x4 ^= wKey[84];
    x2 ^= wKey[85];
    x1 ^= wKey[86];
    x0 ^= wKey[87];
    sbox5();
    x2 ^= wKey[88];
    x0 ^= wKey[89];
    x4 ^= wKey[90];
    x1 ^= wKey[91];
    sbox6();
    x2 ^= wKey[92];
    x0 ^= wKey[93];
    x3 ^= wKey[94];
    x4 ^= wKey[95];
    sbox7();
    x0 = x3;
    x3 = x2;
    x2 = x4;
    x0 ^= wKey[96];
    x1 ^= wKey[97];
    x2 ^= wKey[98];
    x3 ^= wKey[99];
    sbox0();
    x1 ^= wKey[100];
    x4 ^= wKey[101];
    x2 ^= wKey[102];
    x0 ^= wKey[103];
    sbox1();
    x0 ^= wKey[104];
    x4 ^= wKey[105];
    x2 ^= wKey[106];
    x1 ^= wKey[107];
    sbox2();
    x2 ^= wKey[108];
    x1 ^= wKey[109];
    x4 ^= wKey[110];
    x3 ^= wKey[111];
    sbox3();
    x1 ^= wKey[112];
    x4 ^= wKey[113];
    x3 ^= wKey[114];
    x0 ^= wKey[115];
    sbox4();
    x4 ^= wKey[116];
    x2 ^= wKey[117];
    x1 ^= wKey[118];
    x0 ^= wKey[119];
    sbox5();
    x2 ^= wKey[120];
    x0 ^= wKey[121];
    x4 ^= wKey[122];
    x1 ^= wKey[123];
    sbox6();
    x2 ^= wKey[124];
    x0 ^= wKey[125];
    x3 ^= wKey[126];
    x4 ^= wKey[127];
    sbox7noLT();
    x0 = x3;
    x3 = x2;
    x2 = x4;
    x0 ^= wKey[128];
    x1 ^= wKey[129];
    x2 ^= wKey[130];
    x3 ^= wKey[131];
    out[o     ] = (byte) x0;
    out[o +  1] = (byte)(x0 >>> 8);
    out[o +  2] = (byte)(x0 >>> 16);
    out[o +  3] = (byte)(x0 >>> 24);
    out[o +  4] = (byte) x1;
    out[o +  5] = (byte)(x1 >>> 8);
    out[o +  6] = (byte)(x1 >>> 16);
    out[o +  7] = (byte)(x1 >>> 24);
    out[o +  8] = (byte) x2;
    out[o +  9] = (byte)(x2 >>> 8);
    out[o + 10] = (byte)(x2 >>> 16);
    out[o + 11] = (byte)(x2 >>> 24);
    out[o + 12] = (byte) x3;
    out[o + 13] = (byte)(x3 >>> 8);
    out[o + 14] = (byte)(x3 >>> 16);
    out[o + 15] = (byte)(x3 >>> 24);
  }

  /**
   * Decrypt one block of ciphertext.
   *
   * @param in the array containing the input data.
   * @param i offset into the in array the data starts at.
   * @param out the array the output data will be copied into.
   * @param o the offset into the out array the output will start at.
   */
  private void decryptBlock(
      byte[]  in,
      int     i,
      byte[]  out,
      int     o)
  {
    x0 = (in[i     ] & 0xff)
      | (in[i +  1] & 0xff) << 8
      | (in[i +  2] & 0xff) << 16
      | (in[i +  3] & 0xff) << 24;
    x1 = (in[i +  4] & 0xff)
      | (in[i +  5] & 0xff) << 8
      | (in[i +  6] & 0xff) << 16
      | (in[i +  7] & 0xff) << 24;
    x2 = (in[i +  8] & 0xff)
      | (in[i +  9] & 0xff) << 8
      | (in[i + 10] & 0xff) << 16
      | (in[i + 11] & 0xff) << 24;
    x3 = (in[i + 12] & 0xff)
      | (in[i + 13] & 0xff) << 8
      | (in[i + 14] & 0xff) << 16
      | (in[i + 15] & 0xff) << 24;
    x0 ^= wKey[128];
    x1 ^= wKey[129];
    x2 ^= wKey[130];
    x3 ^= wKey[131];
    sboxI7noLT();
    x3 ^= wKey[124];
    x0 ^= wKey[125];
    x1 ^= wKey[126];
    x4 ^= wKey[127];
    sboxI6();
    x0 ^= wKey[120];
    x1 ^= wKey[121];
    x2 ^= wKey[122];
    x4 ^= wKey[123];
    sboxI5();
    x1 ^= wKey[116];
    x3 ^= wKey[117];
    x4 ^= wKey[118];
    x2 ^= wKey[119];
    sboxI4();
    x1 ^= wKey[112];
    x2 ^= wKey[113];
    x4 ^= wKey[114];
    x0 ^= wKey[115];
    sboxI3();
    x0 ^= wKey[108];
    x1 ^= wKey[109];
    x4 ^= wKey[110];
    x2 ^= wKey[111];
    sboxI2();
    x1 ^= wKey[104];
    x3 ^= wKey[105];
    x4 ^= wKey[106];
    x2 ^= wKey[107];
    sboxI1();
    x0 ^= wKey[100];
    x1 ^= wKey[101];
    x2 ^= wKey[102];
    x4 ^= wKey[103];
    sboxI0();
    x0 ^= wKey[96];
    x3 ^= wKey[97];
    x1 ^= wKey[98];
    x4 ^= wKey[99];
    sboxI7();
    x1 = x3;
    x3 = x4;
    x4 = x2;
    x3 ^= wKey[92];
    x0 ^= wKey[93];
    x1 ^= wKey[94];
    x4 ^= wKey[95];
    sboxI6();
    x0 ^= wKey[88];
    x1 ^= wKey[89];
    x2 ^= wKey[90];
    x4 ^= wKey[91];
    sboxI5();
    x1 ^= wKey[84];
    x3 ^= wKey[85];
    x4 ^= wKey[86];
    x2 ^= wKey[87];
    sboxI4();
    x1 ^= wKey[80];
    x2 ^= wKey[81];
    x4 ^= wKey[82];
    x0 ^= wKey[83];
    sboxI3();
    x0 ^= wKey[76];
    x1 ^= wKey[77];
    x4 ^= wKey[78];
    x2 ^= wKey[79];
    sboxI2();
    x1 ^= wKey[72];
    x3 ^= wKey[73];
    x4 ^= wKey[74];
    x2 ^= wKey[75];
    sboxI1();
    x0 ^= wKey[68];
    x1 ^= wKey[69];
    x2 ^= wKey[70];
    x4 ^= wKey[71];
    sboxI0();
    x0 ^= wKey[64];
    x3 ^= wKey[65];
    x1 ^= wKey[66];
    x4 ^= wKey[67];
    sboxI7();
    x1 = x3;
    x3 = x4;
    x4 = x2;
    x3 ^= wKey[60];
    x0 ^= wKey[61];
    x1 ^= wKey[62];
    x4 ^= wKey[63];
    sboxI6();
    x0 ^= wKey[56];
    x1 ^= wKey[57];
    x2 ^= wKey[58];
    x4 ^= wKey[59];
    sboxI5();
    x1 ^= wKey[52];
    x3 ^= wKey[53];
    x4 ^= wKey[54];
    x2 ^= wKey[55];
    sboxI4();
    x1 ^= wKey[48];
    x2 ^= wKey[49];
    x4 ^= wKey[50];
    x0 ^= wKey[51];
    sboxI3();
    x0 ^= wKey[44];
    x1 ^= wKey[45];
    x4 ^= wKey[46];
    x2 ^= wKey[47];
    sboxI2();
    x1 ^= wKey[40];
    x3 ^= wKey[41];
    x4 ^= wKey[42];
    x2 ^= wKey[43];
    sboxI1();
    x0 ^= wKey[36];
    x1 ^= wKey[37];
    x2 ^= wKey[38];
    x4 ^= wKey[39];
    sboxI0();
    x0 ^= wKey[32];
    x3 ^= wKey[33];
    x1 ^= wKey[34];
    x4 ^= wKey[35];
    sboxI7();
    x1 = x3;
    x3 = x4;
    x4 = x2;
    x3 ^= wKey[28];
    x0 ^= wKey[29];
    x1 ^= wKey[30];
    x4 ^= wKey[31];
    sboxI6();
    x0 ^= wKey[24];
    x1 ^= wKey[25];
    x2 ^= wKey[26];
    x4 ^= wKey[27];
    sboxI5();
    x1 ^= wKey[20];
    x3 ^= wKey[21];
    x4 ^= wKey[22];
    x2 ^= wKey[23];
    sboxI4();
    x1 ^= wKey[16];
    x2 ^= wKey[17];
    x4 ^= wKey[18];
    x0 ^= wKey[19];
    sboxI3();
    x0 ^= wKey[12];
    x1 ^= wKey[13];
    x4 ^= wKey[14];
    x2 ^= wKey[15];
    sboxI2();
    x1 ^= wKey[8];
    x3 ^= wKey[9];
    x4 ^= wKey[10];
    x2 ^= wKey[11];
    sboxI1();
    x0 ^= wKey[4];
    x1 ^= wKey[5];
    x2 ^= wKey[6];
    x4 ^= wKey[7];
    sboxI0();
    x2 = x1;
    x1 = x3;
    x3 = x4;
    x0 ^= wKey[0];
    x1 ^= wKey[1];
    x2 ^= wKey[2];
    x3 ^= wKey[3];
    out[o     ] = (byte) x0;
    out[o +  1] = (byte)(x0 >>> 8);
    out[o +  2] = (byte)(x0 >>> 16);
    out[o +  3] = (byte)(x0 >>> 24);
    out[o +  4] = (byte) x1;
    out[o +  5] = (byte)(x1 >>> 8);
    out[o +  6] = (byte)(x1 >>> 16);
    out[o +  7] = (byte)(x1 >>> 24);
    out[o +  8] = (byte) x2;
    out[o +  9] = (byte)(x2 >>> 8);
    out[o + 10] = (byte)(x2 >>> 16);
    out[o + 11] = (byte)(x2 >>> 24);
    out[o + 12] = (byte) x3;
    out[o + 13] = (byte)(x3 >>> 8);
    out[o + 14] = (byte)(x3 >>> 16);
    out[o + 15] = (byte)(x3 >>> 24);
  }

  // These first few S-boxes operate directly on the "registers",
  // x0..x4, and perform the linear transform.
  private void sbox0()
  {
    x3 ^= x0;
    x4 = x1;
    x1 &= x3;
    x4 ^= x2;
    x1 ^= x0;
    x0 |= x3;
    x0 ^= x4;
    x4 ^= x3;
    x3 ^= x2;
    x2 |= x1;
    x2 ^= x4;
    x4 ^= -1;
    x4 |= x1;
    x1 ^= x3;
    x1 ^= x4;
    x3 |= x0;
    x1 ^= x3;
    x4 ^= x3;

    x1 = (x1 << 13) | (x1 >>> 19);
    x4 ^= x1;
    x3 = x1 << 3;
    x2 = (x2 << 3) | (x2 >>> 29);
    x4 ^= x2;
    x0 ^= x2;
    x4 = (x4 << 1) | (x4 >>> 31);
    x0 ^= x3;
    x0 = (x0 << 7) | (x0 >>> 25);
    x3 = x4;
    x1 ^= x4;
    x3 <<= 7;
    x1 ^= x0;
    x2 ^= x0;
    x2 ^= x3;
    x1 = (x1 << 5) | (x1 >>> 27);
    x2 = (x2 << 22) | (x2 >>> 10);
  }

  private void sbox1()
  {
    x4 = ~x4;
    x3 = x1;
    x1 ^= x4;
    x3 |= x4;
    x3 ^= x0;
    x0 &= x1;
    x2 ^= x3;
    x0 ^= x4;
    x0 |= x2;
    x1 ^= x3;
    x0 ^= x1;
    x4 &= x2;
    x1 |= x4;
    x4 ^= x3;
    x1 ^= x2;
    x3 |= x0;
    x1 ^= x3;
    x3 = ~x3;
    x4 ^= x0;
    x3 &= x2;
    x4 = ~x4;
    x3 ^= x1;
    x4 ^= x3;

    x0 = (x0 << 13) | (x0 >>> 19);
    x4 ^= x0;
    x3 = x0 << 3;
    x2 = (x2 << 3) | (x2 >>> 29);
    x4 ^= x2;
    x1 ^= x2;
    x4 = (x4 << 1) | (x4 >>> 31);
    x1 ^= x3;
    x1 = (x1 << 7) | (x1 >>> 25);
    x3 = x4;
    x0 ^= x4;
    x3 <<= 7;
    x0 ^= x1;
    x2 ^= x1;
    x2 ^= x3;
    x0 = (x0 << 5) | (x0 >>> 27);
    x2 = (x2 << 22) | (x2 >>> 10);
  }

  private void sbox2()
  {
    x3 = x0;
    x0 = x0 & x2;
    x0 = x0 ^ x1;
    x2 = x2 ^ x4;
    x2 = x2 ^ x0;
    x1 = x1 | x3;
    x1 = x1 ^ x4;
    x3 = x3 ^ x2;
    x4 = x1;
    x1 = x1 | x3;
    x1 = x1 ^ x0;
    x0 = x0 & x4;
    x3 = x3 ^ x0;
    x4 = x4 ^ x1;
    x4 = x4 ^ x3;
    x3 = ~x3;

    x2 = (x2 << 13) | (x2 >>> 19);
    x1 ^= x2;
    x0 = x2 << 3;
    x4 = (x4 << 3) | (x4 >>> 29);
    x1 ^= x4;
    x3 ^= x4;
    x1 = (x1 << 1) | (x1 >>> 31);
    x3 ^= x0;
    x3 = (x3 << 7) | (x3 >>> 25);
    x0 = x1;
    x2 ^= x1;
    x0 <<= 7;
    x2 ^= x3;
    x4 ^= x3;
    x4 ^= x0;
    x2 = (x2 << 5) | (x2 >>> 27);
    x4 = (x4 << 22) | (x4 >>> 10);
  }

  private void sbox3()
  {
    x0 = x2;
    x2 = x2 | x3;
    x3 = x3 ^ x1;
    x1 = x1 & x0;
    x0 = x0 ^ x4;
    x4 = x4 ^ x3;
    x3 = x3 & x2;
    x0 = x0 | x1;
    x3 = x3 ^ x0;
    x2 = x2 ^ x1;
    x0 = x0 & x2;
    x1 = x1 ^ x3;
    x0 = x0 ^ x4;
    x1 = x1 | x2;
    x1 = x1 ^ x4;
    x2 = x2 ^ x3;
    x4 = x1;
    x1 = x1 | x3;
    x1 = x1 ^ x2;

    x1 = (x1 << 13) | (x1 >>> 19);
    x4 ^= x1;
    x2 = x1 << 3;
    x3 = (x3 << 3) | (x3 >>> 29);
    x4 ^= x3;
    x0 ^= x3;
    x4 = (x4 << 1) | (x4 >>> 31);
    x0 ^= x2;
    x0 = (x0 << 7) | (x0 >>> 25);
    x2 = x4;
    x1 ^= x4;
    x2 <<= 7;
    x1 ^= x0;
    x3 ^= x0;
    x3 ^= x2;
    x1 = (x1 << 5) | (x1 >>> 27);
    x3 = (x3 << 22) | (x3 >>> 10);
  }

  private void sbox4()
  {
    x4 = x4 ^ x0;
    x0 = ~x0;
    x3 = x3 ^ x0;
    x0 = x0 ^ x1;
    x2 = x4;
    x4 = x4 & x0;
    x4 = x4 ^ x3;
    x2 = x2 ^ x0;
    x1 = x1 ^ x2;
    x3 = x3 & x2;
    x3 = x3 ^ x1;
    x1 = x1 & x4;
    x0 = x0 ^ x1;
    x2 = x2 | x4;
    x2 = x2 ^ x1;
    x1 = x1 | x0;
    x1 = x1 ^ x3;
    x3 = x3 & x0;
    x1 = ~x1;
    x2 = x2 ^ x3;

    x4 = (x4 << 13) | (x4 >>> 19);
    x2 ^= x4;
    x3 = x4 << 3;
    x1 = (x1 << 3) | (x1 >>> 29);
    x2 ^= x1;
    x0 ^= x1;
    x2 = (x2 << 1) | (x2 >>> 31);
    x0 ^= x3;
    x0 = (x0 << 7) | (x0 >>> 25);
    x3 = x2;
    x4 ^= x2;
    x3 <<= 7;
    x4 ^= x0;
    x1 ^= x0;
    x1 ^= x3;
    x4 = (x4 << 5) | (x4 >>> 27);
    x1 = (x1 << 22) | (x1 >>> 10);
  }

  private void sbox5()
  {
    x4 = x4 ^ x2;
    x2 = x2 ^ x0;
    x0 = ~x0;
    x3 = x2;
    x2 = x2 & x4;
    x1 = x1 ^ x0;
    x2 = x2 ^ x1;
    x1 = x1 | x3;
    x3 = x3 ^ x0;
    x0 = x0 & x2;
    x0 = x0 ^ x4;
    x3 = x3 ^ x2;
    x3 = x3 ^ x1;
    x1 = x1 ^ x4;
    x4 = x4 & x0;
    x1 = ~x1;
    x4 = x4 ^ x3;
    x3 = x3 | x0;
    x1 = x1 ^ x3;

    x2 = (x2 << 13) | (x2 >>> 19);
    x0 ^= x2;
    x3 = x2 << 3;
    x4 = (x4 << 3) | (x4 >>> 29);
    x0 ^= x4;
    x1 ^= x4;
    x0 = (x0 << 1) | (x0 >>> 31);
    x1 ^= x3;
    x1 = (x1 << 7) | (x1 >>> 25);
    x3 = x0;
    x2 ^= x0;
    x3 <<= 7;
    x2 ^= x1;
    x4 ^= x1;
    x4 ^= x3;
    x2 = (x2 << 5) | (x2 >>> 27);
    x4 = (x4 << 22) | (x4 >>> 10);
  }

  private void sbox6()
  {
    x4 = ~x4;
    x3 = x1;
    x1 = x1 & x2;
    x2 = x2 ^ x3;
    x1 = x1 ^ x4;
    x4 = x4 | x3;
    x0 = x0 ^ x1;
    x4 = x4 ^ x2;
    x2 = x2 | x0;
    x4 = x4 ^ x0;
    x3 = x3 ^ x2;
    x2 = x2 | x1;
    x2 = x2 ^ x4;
    x3 = x3 ^ x1;
    x3 = x3 ^ x2;
    x1 = ~x1;
    x4 = x4 & x3;
    x4 = x4 ^ x1;
    x2 = (x2 << 13) | (x2 >>> 19);
    x0 ^= x2;
    x1 = x2 << 3;
    x3 = (x3 << 3) | (x3 >>> 29);
    x0 ^= x3;
    x4 ^= x3;
    x0 = (x0 << 1) | (x0 >>> 31);
    x4 ^= x1;
    x4 = (x4 << 7) | (x4 >>> 25);
    x1 = x0;
    x2 ^= x0;
    x1 <<= 7;
    x2 ^= x4;
    x3 ^= x4;
    x3 ^= x1;
    x2 = (x2 << 5) | (x2 >>> 27);
    x3 = (x3 << 22) | (x3 >>> 10);
  }

  private void sbox7()
  {
    x1 = x3;
    x3 = x3 & x0;
    x3 = x3 ^ x4;
    x4 = x4 & x0;
    x1 = x1 ^ x3;
    x3 = x3 ^ x0;
    x0 = x0 ^ x2;
    x2 = x2 | x1;
    x2 = x2 ^ x3;
    x4 = x4 ^ x0;
    x3 = x3 ^ x4;
    x4 = x4 & x2;
    x4 = x4 ^ x1;
    x1 = x1 ^ x3;
    x3 = x3 & x2;
    x1 = ~x1;
    x3 = x3 ^ x1;
    x1 = x1 & x2;
    x0 = x0 ^ x4;
    x1 = x1 ^ x0;
    x3 = (x3 << 13) | (x3 >>> 19);
    x1 ^= x3;
    x0 = x3 << 3;
    x4 = (x4 << 3) | (x4 >>> 29);
    x1 ^= x4;
    x2 ^= x4;
    x1 = (x1 << 1) | (x1 >>> 31);
    x2 ^= x0;
    x2 = (x2 << 7) | (x2 >>> 25);
    x0 = x1;
    x3 ^= x1;
    x0 <<= 7;
    x3 ^= x2;
    x4 ^= x2;
    x4 ^= x0;
    x3 = (x3 << 5) | (x3 >>> 27);
    x4 = (x4 << 22) | (x4 >>> 10);
  }

  /** The final S-box, with no transform. */
  private void sbox7noLT()
  {
    x1 = x3;
    x3 = x3 & x0;
    x3 = x3 ^ x4;
    x4 = x4 & x0;
    x1 = x1 ^ x3;
    x3 = x3 ^ x0;
    x0 = x0 ^ x2;
    x2 = x2 | x1;
    x2 = x2 ^ x3;
    x4 = x4 ^ x0;
    x3 = x3 ^ x4;
    x4 = x4 & x2;
    x4 = x4 ^ x1;
    x1 = x1 ^ x3;
    x3 = x3 & x2;
    x1 = ~x1;
    x3 = x3 ^ x1;
    x1 = x1 & x2;
    x0 = x0 ^ x4;
    x1 = x1 ^ x0;
  }

  private void sboxI7noLT()
  {
    x4 = x2;
    x2 ^= x0;
    x0 &= x3;
    x2 = ~x2;
    x4 |= x3;
    x3 ^= x1;
    x1 |= x0;
    x0 ^= x2;
    x2 &= x4;
    x1 ^= x2;
    x2 ^= x0;
    x0 |= x2;
    x3 &= x4;
    x0 ^= x3;
    x4 ^= x1;
    x3 ^= x4;
    x4 |= x0;
    x3 ^= x2;
    x4 ^= x2;
  }

  private void sboxI6()
  {
    x1 = (x1 >>> 22) | (x1 << 10);
    x3 = (x3 >>> 5) | (x3 << 27);
    x2 = x0;
    x1 ^= x4;
    x2 <<= 7;
    x3 ^= x4;
    x1 ^= x2;
    x3 ^= x0;
    x4 = (x4 >>> 7) | (x4 << 25);
    x0 = (x0 >>> 1) | (x0 << 31);
    x0 ^= x3;
    x2 = x3 << 3;
    x4 ^= x2;
    x3 = (x3 >>> 13) | (x3 << 19);
    x0 ^= x1;
    x4 ^= x1;
    x1 = (x1 >>> 3) | (x1 << 29);
    x3 ^= x1;
    x2 = x1;
    x1 &= x3;
    x2 ^= x4;
    x1 = ~x1;
    x4 ^= x0;
    x1 ^= x4;
    x2 |= x3;
    x3 ^= x1;
    x4 ^= x2;
    x2 ^= x0;
    x0 &= x4;
    x0 ^= x3;
    x3 ^= x4;
    x3 |= x1;
    x4 ^= x0;
    x2 ^= x3;
  }

  private void sboxI5()
  {
    x2 = (x2 >>> 22) | (x2 << 10);
    x0 = (x0 >>> 5) | (x0 << 27);
    x3 = x1;
    x2 ^= x4;
    x3 <<= 7;
    x0 ^= x4;
    x2 ^= x3;
    x0 ^= x1;
    x4 = (x4 >>> 7) | (x4 << 25);
    x1 = (x1 >>> 1) | (x1 << 31);
    x1 ^= x0;
    x3 = x0 << 3;
    x4 ^= x3;
    x0 = (x0 >>> 13) | (x0 << 19);
    x1 ^= x2;
    x4 ^= x2;
    x2 = (x2 >>> 3) | (x2 << 29);
    x1 = ~x1;
    x3 = x4;
    x2 ^= x1;
    x4 |= x0;
    x4 ^= x2;
    x2 |= x1;
    x2 &= x0;
    x3 ^= x4;
    x2 ^= x3;
    x3 |= x0;
    x3 ^= x1;
    x1 &= x2;
    x1 ^= x4;
    x3 ^= x2;
    x4 &= x3;
    x3 ^= x1;
    x4 ^= x0;
    x4 ^= x3;
    x3 = ~x3;
  }

  private void sboxI4()
  {
    x4 = (x4 >>> 22) | (x4 << 10);
    x1 = (x1 >>> 5) | (x1 << 27);
    x0 = x3;
    x4 ^= x2;
    x0 <<= 7;
    x1 ^= x2;
    x4 ^= x0;
    x1 ^= x3;
    x2 = (x2 >>> 7) | (x2 << 25);
    x3 = (x3 >>> 1) | (x3 << 31);
    x3 ^= x1;
    x0 = x1 << 3;
    x2 ^= x0;
    x1 = (x1 >>> 13) | (x1 << 19);
    x3 ^= x4;
    x2 ^= x4;
    x4 = (x4 >>> 3) | (x4 << 29);
    x0 = x4;
    x4 &= x2;
    x4 ^= x3;
    x3 |= x2;
    x3 &= x1;
    x0 ^= x4;
    x0 ^= x3;
    x3 &= x4;
    x1 = ~x1;
    x2 ^= x0;
    x3 ^= x2;
    x2 &= x1;
    x2 ^= x4;
    x1 ^= x3;
    x4 &= x1;
    x2 ^= x1;
    x4 ^= x0;
    x4 |= x2;
    x2 ^= x1;
    x4 ^= x3;
  }

  private void sboxI3()
  {
    x4 = (x4 >>> 22) | (x4 << 10);
    x1 = (x1 >>> 5) | (x1 << 27);
    x3 = x2;
    x4 ^= x0;
    x3 <<= 7;
    x1 ^= x0;
    x4 ^= x3;
    x1 ^= x2;
    x0 = (x0 >>> 7) | (x0 << 25);
    x2 = (x2 >>> 1) | (x2 << 31);
    x2 ^= x1;
    x3 = x1 << 3;
    x0 ^= x3;
    x1 = (x1 >>> 13) | (x1 << 19);
    x2 ^= x4;
    x0 ^= x4;
    x4 = (x4 >>> 3) | (x4 << 29);
    x3 = x4;
    x4 ^= x2;
    x2 &= x4;
    x2 ^= x1;
    x1 &= x3;
    x3 ^= x0;
    x0 |= x2;
    x0 ^= x4;
    x1 ^= x3;
    x4 ^= x1;
    x1 |= x0;
    x1 ^= x2;
    x3 ^= x4;
    x4 &= x0;
    x2 |= x0;
    x2 ^= x4;
    x3 ^= x1;
    x4 ^= x3;
  }

  private void sboxI2()
  {
    x4 = (x4 >>> 22) | (x4 << 10);
    x0 = (x0 >>> 5) | (x0 << 27);
    x3 = x1;
    x4 ^= x2;
    x3 <<= 7;
    x0 ^= x2;
    x4 ^= x3;
    x0 ^= x1;
    x2 = (x2 >>> 7) | (x2 << 25);
    x1 = (x1 >>> 1) | (x1 << 31);
    x1 ^= x0;
    x3 = x0 << 3;
    x2 ^= x3;
    x0 = (x0 >>> 13) | (x0 << 19);
    x1 ^= x4;
    x2 ^= x4;
    x4 = (x4 >>> 3) | (x4 << 29);
    x4 ^= x2;
    x2 ^= x0;
    x3 = x2;
    x2 &= x4;
    x2 ^= x1;
    x1 |= x4;
    x1 ^= x3;
    x3 &= x2;
    x4 ^= x2;
    x3 &= x0;
    x3 ^= x4;
    x4 &= x1;
    x4 |= x0;
    x2 = ~x2;
    x4 ^= x2;
    x0 ^= x2;
    x0 &= x1;
    x2 ^= x3;
    x2 ^= x0;
  }

  private void sboxI1()
  {
    x4 = (x4 >>> 22) | (x4 << 10);
    x1 = (x1 >>> 5) | (x1 << 27);
    x0 = x3;
    x4 ^= x2;
    x0 <<= 7;
    x1 ^= x2;
    x4 ^= x0;
    x1 ^= x3;
    x2 = (x2 >>> 7) | (x2 << 25);
    x3 = (x3 >>> 1) | (x3 << 31);
    x3 ^= x1;
    x0 = x1 << 3;
    x2 ^= x0;
    x1 = (x1 >>> 13) | (x1 << 19);
    x3 ^= x4;
    x2 ^= x4;
    x4 = (x4 >>> 3) | (x4 << 29);
    x0 = x3;
    x3 ^= x2;
    x2 &= x3;
    x0 ^= x4;
    x2 ^= x1;
    x1 |= x3;
    x4 ^= x2;
    x1 ^= x0;
    x1 |= x4;
    x3 ^= x2;
    x1 ^= x3;
    x3 |= x2;
    x3 ^= x1;
    x0 = ~x0;
    x0 ^= x3;
    x3 |= x1;
    x3 ^= x1;
    x3 |= x0;
    x2 ^= x3;
  }

  private void sboxI0()
  {
    x2 = (x2 >>> 22) | (x2 << 10);
    x0 = (x0 >>> 5) | (x0 << 27);
    x3 = x1;
    x2 ^= x4;
    x3 <<= 7;
    x0 ^= x4;
    x2 ^= x3;
    x0 ^= x1;
    x4 = (x4 >>> 7) | (x4 << 25);
    x1 = (x1 >>> 1) | (x1 << 31);
    x1 ^= x0;
    x3 = x0 << 3;
    x4 ^= x3;
    x0 = (x0 >>> 13) | (x0 << 19);
    x1 ^= x2;
    x4 ^= x2;
    x2 = (x2 >>> 3) | (x2 << 29);
    x2 = ~x2;
    x3 = x1;
    x1 |= x0;
    x3 = ~x3;
    x1 ^= x2;
    x2 |= x3;
    x1 ^= x4;
    x0 ^= x3;
    x2 ^= x0;
    x0 &= x4;
    x3 ^= x0;
    x0 |= x1;
    x0 ^= x2;
    x4 ^= x3;
    x2 ^= x1;
    x4 ^= x0;
    x4 ^= x1;
    x2 &= x4;
    x3 ^= x2;
  }

  private void sboxI7()
  {
    x1 = (x1 >>> 22) | (x1 << 10);
    x0 = (x0 >>> 5) | (x0 << 27);
    x2 = x3;
    x1 ^= x4;
    x2 <<= 7;
    x0 ^= x4;
    x1 ^= x2;
    x0 ^= x3;
    x4 = (x4 >>> 7) | (x4 << 25);
    x3 = (x3 >>> 1) | (x3 << 31);
    x3 ^= x0;
    x2 = x0 << 3;
    x4 ^= x2;
    x0 = (x0 >>> 13) | (x0 << 19);
    x3 ^= x1;
    x4 ^= x1;
    x1 = (x1 >>> 3) | (x1 << 29);
    x2 = x1;
    x1 ^= x0;
    x0 &= x4;
    x1 = ~x1;
    x2 |= x4;
    x4 ^= x3;
    x3 |= x0;
    x0 ^= x1;
    x1 &= x2;
    x3 ^= x1;
    x1 ^= x0;
    x0 |= x1;
    x4 &= x2;
    x0 ^= x4;
    x2 ^= x3;
    x4 ^= x2;
    x2 |= x0;
    x4 ^= x1;
    x2 ^= x1;
  }

  /** S-Box 0. */
  private void sbox0(int r0, int r1, int r2, int r3)
  {
    int r4 = r1 ^ r2;
    r3 ^= r0;
    r1 = r1 & r3 ^ r0;
    r0 = (r0 | r3) ^ r4;
    r4 ^= r3;
    r3 ^= r2;
    r2 = (r2 | r1) ^ r4;
    r4 = ~r4 | r1;
    r1 ^= r3 ^ r4;
    r3 |= r0;
    x0 = r1 ^ r3;
    x1 = r4 ^ r3;
    x2 = r2;
    x3 = r0;
  }

  /** S-Box 1. */
  private void sbox1(int r0, int r1, int r2, int r3)
  {
    r0 = ~r0;
    int r4 = r0;
    r2 = ~r2;
    r0 &= r1;
    r2 ^= r0;
    r0 |= r3;
    r3 ^= r2;
    r1 ^= r0;
    r0 ^= r4;
    r4 |= r1;
    r1 ^= r3;
    r2 = (r2 | r0) & r4;
    r0 ^= r1;
    x0 = r2;
    x1 = r0 & r2 ^ r4;
    x2 = r3;
    x3 = r1 & r2 ^ r0;
  }

  /** S-Box 2. */
  private void sbox2(int r0, int r1, int r2, int r3)
  {
    int r4 = r0;
    r0 = r0 & r2 ^ r3;
    r2 = r2 ^ r1 ^ r0;
    r3 = (r3 | r4) ^ r1;
    r4 ^= r2;
    r1 = r3;
    r3 = (r3 | r4) ^ r0;
    r0 &= r1;
    r4 ^= r0;
    x0 = r2;
    x1 = r3;
    x2 = r1 ^ r3 ^ r4;
    x3 = ~r4;
  }

  /** S-Box 3. */
  private void sbox3(int r0, int r1, int r2, int r3)
  {
    int r4 = r0;
    r0 |= r3;
    r3 ^= r1;
    r1 &= r4;
    r4 = r4 ^ r2 | r1;
    r2 ^= r3;
    r3 = r3 & r0 ^ r4;
    r0 ^= r1;
    r4 = r4 & r0 ^ r2;
    r1 = (r1 ^ r3 | r0) ^ r2;
    r0 ^= r3;
    x0 = (r1 | r3) ^ r0;
    x1 = r1;
    x2 = r3;
    x3 = r4;
  }

  /** S-Box 4. */
  private void sbox4(int r0, int r1, int r2, int r3)
  {
    r1 ^= r3;
    int r4 = r1;
    r3 = ~r3;
    r2 ^= r3;
    r3 ^= r0;
    r1 = r1 & r3 ^ r2;
    r4 ^= r3;
    r0 ^= r4;
    r2 = r2 & r4 ^ r0;
    r0 &= r1;
    r3 ^= r0;
    r4 = (r4 | r1) ^ r0;
    x0 = r1;
    x1 = r4 ^ (r2 & r3);
    x2 = ~((r0 | r3) ^ r2);
    x3 = r3;
  }

  /** S-Box 5. */
  private void sbox5(int r0, int r1, int r2, int r3)
  {
    r0 ^= r1;
    r1 ^= r3;
    int r4 = r1;
    r3 = ~r3;
    r1 &= r0;
    r2 ^= r3;
    r1 ^= r2;
    r2 |= r4;
    r4 ^= r3;
    r3 = r3 & r1 ^ r0;
    r4 = r4 ^ r1 ^ r2;
    x0 = r1;
    x1 = r3;
    x2 = r0 & r3 ^ r4;
    x3 = ~(r2 ^ r0) ^ (r4 | r3);
  }

  /** S-Box 6. */
  private void sbox6(int r0, int r1, int r2, int r3)
  {
    int r4 = r3;
    r2 = ~r2;
    r3 = r3 & r0 ^ r2;
    r0 ^= r4;
    r2 = (r2 | r4) ^ r0;
    r1 ^= r3;
    r0 |= r1;
    r2 ^= r1;
    r4 ^= r0;
    r0 = (r0 | r3) ^ r2;
    r4 = r4 ^ r3 ^ r0;
    x0 = r0;
    x1 = r1;
    x2 = r4;
    x3 = r2 & r4 ^ ~r3;
  }

  /** S-Box 7. */
  private void sbox7(int r0, int r1, int r2, int r3)
  {
    int r4 = r1;
    r1 = (r1 | r2) ^ r3;
    r4 ^= r2;
    r2 ^= r1;
    r3 = (r3 | r4) & r0;
    r4 ^= r2;
    r3 ^= r1;
    r1 = (r1 | r4) ^ r0;
    r0 = (r0 | r4) ^ r2;
    r1 ^= r4;
    r2 ^= r1;
    x0 = r4 ^ (~r2 | r0);
    x1 = r3;
    x2 = r1 & r0 ^ r4;
    x3 = r0;
  }
}
