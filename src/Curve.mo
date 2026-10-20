/// Elliptic curve parameters and Jacobi-coordinate point arithmetic for
/// secp256k1 and prime256v1 (NIST P-256). Most users should access this
/// module through `mo:ecdsa` rather than directly.
///
/// ```motoko name=import
/// import Curve "mo:ecdsa/Curve";
/// ```

import Array "mo:core@2/Array";
import Debug "mo:core@2/Debug";
import Int "mo:core@2/Int";
import Iter "mo:core@2/Iter";
import Blob "mo:core@2/Blob";
import Nat "mo:core@2/Nat";
import Nat8 "mo:core@2/Nat8";
import VarArray "mo:core@2/VarArray";

import Binary "./Binary";
import Field "./Field";
import Hex "./Hex";
import Util "./Util";

module {
  /// An element of the base field `F_p`, where `p` is the curve's field prime.
  public type FpElt = { #fp : Nat };
  /// An element of the scalar field `F_r`, where `r` is the curve order.
  public type FrElt = { #fr : Nat };
  /// An affine point `(x, y)` on the curve.
  public type Affine = (FpElt, FpElt);
  /// A point on the curve, either the point at infinity (`#zero`) or an
  /// affine point.
  public type Point = { #zero; #affine : Affine };

  type CurveParams = {
    a : FpElt;
    b : FpElt;
    g : (FpElt, FpElt);
    p : Nat;
    r : Nat;
    rHalf : Nat;
    pSqrRoot : Nat;
    kind : CurveKind;
  };

  // GLV endomorphism constants specifically for secp256k1
  private let GLV_CONSTANTS = {
    B00 : Int = 0x3086d221a7d46bcde86c90e49284eb15;
    B01 : Int = -0xe4437ed6010e88286f547fa90abfe4c3;
    B10 : Int = 0x114ca50f7a8e2f3f657c1108d9d44cfd8;
    rw = #fp(55594575648329892869085402983802832744385952214688224221778511981742606582254);
    SHIFT256 : Int = 0x10000000000000000000000000000000000000000000000000000000000000000;
    v0 : Int = 64502973549206556628585045361533709077;
    v1 : Int = 303414439467246543595250775667605759172;
  };

  /// A point in Jacobi (a.k.a. Jacobian) projective coordinates `(X, Y, Z)`,
  /// representing the affine point `(X/Z^2, Y/Z^3)` when `Z != 0`, and the
  /// point at infinity when `Z == 0`. Used internally to avoid expensive
  /// modular inversions during chained operations.
  public type Jacobi = (FpElt, FpElt, FpElt);

  /// The supported short Weierstrass curves.
  /// `#secp256k1` is the Bitcoin / ICP curve (`y^2 = x^3 + 7`).
  /// `#prime256v1` is NIST P-256 (`y^2 = x^3 - 3x + b`).
  public type CurveKind = {
    #secp256k1;
    #prime256v1;
  };

  /// Holds the parameters and arithmetic operations for one of the
  /// supported curves. Constructing a `Curve` allocates parameter tables;
  /// reuse the same instance across many keys and signatures.
  public class Curve(kind_ : CurveKind) {
    /// Which curve this instance represents.
    public let kind = kind_;
    /// The full parameter set for `kind` (field prime, order, generator,
    /// etc.).
    public let params : CurveParams = getParams(kind);
    let p_ = params.p;
    let r_ = params.r;
    let a_ = params.a;
    let b_ = params.b;

    // Check if the curve supports GLV endomorphism
    let hasGLV = switch (kind) {
      case (#secp256k1) true;
      case (#prime256v1) false;
    };
    // GLV endomorphism constant beta (secp256k1 only):
    // `lambda * (x, y) = (beta * x, y)`.
    let glvBeta : Nat = switch (GLV_CONSTANTS.rw) { case (#fp(b)) b };

    // Fast pseudo-Mersenne reduction modulo the secp256k1 prime
    // p = 2^256 - C, where C = 2^32 + 977.
    //
    // For any t with 0 <= t < p^2 (e.g. the result of multiplying two
    // reduced field elements), 2^256 ≡ C (mod p) gives
    //
    //   t  ≡  t_lo + t_hi * C  (mod p),  where t = t_hi * 2^256 + t_lo.
    //
    // Two passes are enough to bring the value below 2 * 2^256, after
    // which a single conditional subtraction of p produces the canonical
    // representative. The high half is extracted with `Nat.bitshiftRight`
    // (mapped to `Prim.shiftRight`), and the low half is recovered as
    // `t - (t_hi << 256)` to avoid a general modulo operation.
    let SECP_C : Nat = 0x1000003D1; // 2^32 + 977
    func reduceSecp(t : Nat) : Nat {
      // First pass: t_hi < 2^256, so t_hi * C < 2^289 and u < 2^290.
      let tHi = Nat.bitshiftRight(t, 256);
      let tLo : Nat = t - Nat.bitshiftLeft(tHi, 256);
      let u = tLo + tHi * SECP_C;
      // Second pass: u_hi < 2^34, so u_hi * C < 2^67 and v < 2^256 + 2^67.
      let uHi = Nat.bitshiftRight(u, 256);
      let uLo : Nat = u - Nat.bitshiftLeft(uHi, 256);
      let v = uLo + uHi * SECP_C;
      if (v >= p_) v - p_ else v;
    };

    // Per-curve `Fp.mul` and `Fp.sqr`: secp256k1 uses the pseudo-Mersenne
    // shortcut above; prime256v1 falls back to generic `Field.mul_`.
    let fpMulNat : (Nat, Nat) -> Nat = switch (kind) {
      case (#secp256k1) (func(x, y) = reduceSecp(x * y));
      case (#prime256v1) (func(x, y) = Field.mul_(x, y, p_));
    };
    let fpSqrNat : Nat -> Nat = switch (kind) {
      case (#secp256k1) (func(x) = reduceSecp(x * x));
      case (#prime256v1) (func(x) = Field.sqr_(x, p_));
    };

    // ===== Montgomery-form arithmetic for prime256v1 =====
    //
    // p-256 has no compact pseudo-Mersenne form, so the scalar-mul hot
    // loop is run in the Montgomery domain instead. Values stored as
    // `aM = a * R mod p`, with `R = 2^256`. Multiplication uses REDC,
    // implemented here using `Nat.bitshiftRight` / `Nat.bitshiftLeft`
    // (which map to `Prim.shiftRight` / `Prim.shiftLeft` and are fast)
    // rather than the generic `% R` / `/ R`, which on `Nat` go through
    // the slow general-bignum-division path.
    //
    // Constants are computed once per `Curve` instance. They are only
    // meaningful for `#prime256v1`; the `#secp256k1` instance fills the
    // slots with zeros and never invokes the Mont-form routines.
    let isP256 = kind == #prime256v1;

    // (-p^{-1}) mod 2^256, via Newton iteration on an odd modulus:
    // start with x = 1 (correct mod 2 since p is odd) and iterate
    // x := x * (2 - p*x) mod 2^256, doubling correct bits each step.
    func computePPrime() : Nat {
      if (not isP256) return 0;
      var x : Nat = 1;
      var k : Nat = 1;
      while (k < 256) {
        let nx = p_ * x;
        let nxLo : Nat = nx - Nat.bitshiftLeft(Nat.bitshiftRight(nx, 256), 256);
        // 2 - nxLo (mod 2^256), avoiding negative intermediates.
        let twoMinus = if (nxLo <= 2) (2 - nxLo : Nat) else (
          // 2^256 + 2 - nxLo
          (Nat.bitshiftLeft(1, 256) + 2 - nxLo : Nat),
        );
        let xnew = x * twoMinus;
        x := xnew - Nat.bitshiftLeft(Nat.bitshiftRight(xnew, 256), 256);
        k *= 2;
      };
      // x ≡ p^{-1} mod R; return (-x) mod R.
      if (x == 0) 0 else Nat.bitshiftLeft(1, 256) - x;
    };

    let pPrime : Nat = computePPrime();
    // R mod p
    let oneM : Nat = if (isP256) {
      let R = Nat.bitshiftLeft(1, 256);
      R % p_;
    } else 0;
    // R^2 mod p, used to enter the Mont domain.
    let R2M : Nat = if (isP256) {
      let R = Nat.bitshiftLeft(1, 256);
      (R * R) % p_;
    } else 0;

    // Montgomery reduction. Given t with 0 <= t < p * R, returns
    // t * R^{-1} mod p, fully reduced (< p).
    func redcP(t : Nat) : Nat {
      let tLo : Nat = t - Nat.bitshiftLeft(Nat.bitshiftRight(t, 256), 256);
      let m = pPrime * tLo;
      let mLo : Nat = m - Nat.bitshiftLeft(Nat.bitshiftRight(m, 256), 256);
      let u = Nat.bitshiftRight(t + mLo * p_, 256);
      if (u >= p_) u - p_ else u;
    };

    // Conversions into and out of the Montgomery domain.
    func toMontP(a : Nat) : Nat = redcP(a * R2M);
    func fromMontP(a : Nat) : Nat = redcP(a);

    /// Returns the bit-width of the curve's field. Both supported curves
    /// are 256-bit, so the only possible value is `#b256`. Reserved as a
    /// variant for future curves.
    public func getBitSize() : { #b256 } = switch (kind) {
      case (#secp256k1 or #prime256v1) #b256;
    };

    /// Modular arithmetic on the base field `F_p`. Each operation takes
    /// `FpElt` values that are assumed to be already reduced modulo `p`.
    public let Fp = {
      fromNat = func(n : Nat) : FpElt = #fp(n % p_);
      toNat = func(#fp(x) : FpElt) : Nat = x;
      add = func(#fp(x) : FpElt, #fp(y) : FpElt) : FpElt = #fp(Field.add_(x, y, p_));
      mul = func(#fp(x) : FpElt, #fp(y) : FpElt) : FpElt = #fp(fpMulNat(x, y));
      sub = func(#fp(x) : FpElt, #fp(y) : FpElt) : FpElt = #fp(Field.sub_(x, y, p_));
      div = func(#fp(x) : FpElt, #fp(y) : FpElt) : FpElt = #fp(Field.div_(x, y, p_));
      pow = func(#fp(x) : FpElt, n : Nat) : FpElt = #fp(Field.pow_(x, n, p_));
      neg = func(#fp(x) : FpElt) : FpElt = #fp(Field.neg_(x, p_));
      inv = func(#fp(x) : FpElt) : FpElt = #fp(Field.inv_(x, p_));
      sqr = func(#fp(x) : FpElt) : FpElt = #fp(fpSqrNat(x));
    };

    /// Modular arithmetic on the scalar field `F_r` (where `r` is the
    /// curve order). Each operation takes `FrElt` values that are assumed
    /// to be already reduced modulo `r`.
    public let Fr = {
      fromNat = func(n : Nat) : FrElt = #fr(n % r_);
      toNat = func(#fr(x) : FrElt) : Nat = x;
      add = func(#fr(x) : FrElt, #fr(y) : FrElt) : FrElt = #fr(Field.add_(x, y, r_));
      mul = func(#fr(x) : FrElt, #fr(y) : FrElt) : FrElt = #fr(Field.mul_(x, y, r_));
      sub = func(#fr(x) : FrElt, #fr(y) : FrElt) : FrElt = #fr(Field.sub_(x, y, r_));
      div = func(#fr(x) : FrElt, #fr(y) : FrElt) : FrElt = #fr(Field.div_(x, y, r_));
      pow = func(#fr(x) : FrElt, n : Nat) : FrElt = #fr(Field.pow_(x, n, r_));
      neg = func(#fr(x) : FrElt) : FrElt = #fr(Field.neg_(x, r_));
      inv = func(#fr(x) : FrElt) : FrElt = #fr(Field.inv_(x, r_));
      sqr = func(#fr(x) : FrElt) : FrElt = #fr(Field.sqr_(x, r_));
    };

    /// Returns `true` when `other` represents the same curve.
    public func equal(other : Curve) : Bool {
      kind == other.kind;
    };

    /// Computes a square root of `x` in `F_p` using the curve's precomputed
    /// `(p+1)/4` exponent. Returns `null` if `x` is not a quadratic
    /// residue. Only correct for primes with `p ≡ 3 (mod 4)`, which both
    /// supported curves satisfy.
    public func fpSqrRoot(#fp(x) : FpElt) : ?FpElt {
      // Square-and-multiply in the working domain (fast reduction).
      let xn = toN(x);
      var s = oneN;
      for (byte in pSqrRootBytes.values()) {
        var bit : Nat8 = 0x80;
        while (bit != 0) {
          s := fsqr(s);
          if (byte & bit != 0) s := fmul(s, xn);
          bit >>= 1;
        };
      };
      if (fsqr(s) == xn) ?#fp(fromN(s)) else null;
    };
    // The square-root exponent `(p+1)/4` (`params.pSqrRoot`) as 32
    // big-endian bytes, so that its bits can be scanned without bignum
    // operations.
    let pSqrRootBytes : Blob = switch (kind) {
      case (#secp256k1) "\3f\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\bf\ff\ff\0c";
      case (#prime256v1) "\3f\ff\ff\ff\c0\00\00\00\40\00\00\00\00\00\00\00\00\00\00\00\40\00\00\00\00\00\00\00\00\00\00\00";
    };

    /// Reads a 32-byte big-endian integer from `rand` and reduces it
    /// modulo the curve order to yield a scalar. Returns `null` if `rand`
    /// yields fewer than 32 bytes.
    public func getExponent(
      rand : Iter.Iter<Nat8>
    ) : ?FrElt {
      let ?nat = Util.toNatAsBigEndian(rand.take(32)) else return null;
      ?Fr.fromNat(nat);
    };

    /// Computes `y^2 = x^3 + a*x + b` for the given `x`.
    // return x^3 + ax + b
    public func getYsqrFromX(x : FpElt) : FpElt = Fp.add(Fp.mul(Fp.add(Fp.sqr(x), a_), x), b_);

    /// Recovers the `y` coordinate that pairs with `x` on the curve.
    /// Returns `null` if `x` is not a valid x-coordinate (no point on the
    /// curve has this x). The `even` flag selects between the two roots:
    /// returns the one whose lowest bit matches `(if even then 0 else 1)`.
    /// Used when decompressing a SEC1 point.
    /// Get y corresponding to x such that y^2 = x^ + ax + b.
    /// Return even y if `even` is true.
    public func getYfromX(x : FpElt, even : Bool) : ?FpElt {
      let y2 = getYsqrFromX(x);
      switch (fpSqrRoot(y2)) {
        case (null) null;
        case (?y) if (even == ((Fp.toNat(y) % 2) == 0)) ?y else ?Fp.neg(y);
      };
    };

    /// Returns `true` when the affine point `(x, y)` satisfies the curve
    /// equation.
    public func isValidAffine((x, y) : Affine) : Bool = Fp.sqr(y) == getYsqrFromX(x);

    /// The curve's generator `G` in Jacobi form (with `Z = 1`).
    public let G_ = (params.g.0, params.g.1, #fp(1));

    /// The Jacobi representation of the point at infinity (`Z = 0`).
    public let zeroJ = (#fp(0), #fp(0), #fp(0));

    /// Returns `true` when `p` is the point at infinity.
    public func isZero((_, _, z) : Jacobi) : Bool = z == #fp(0);

    /// Lifts a `Point` to its Jacobi representation.
    public func toJacobi(a : Point) : Jacobi = switch (a) {
      case (#zero) zeroJ;
      case (#affine(x, y)) (x, y, #fp(1));
    };

    /// Returns the canonical Jacobi representative with `Z = 1` (or
    /// `Z = 0` for the point at infinity). Performs one modular inversion
    /// of `Z`.
    public func normalize((x, y, z) : Jacobi) : Jacobi {
      if (z == #fp(0)) return (x, y, z);
      let rz = Fp.inv(z);
      let rz2 = Fp.sqr(rz);
      (Fp.mul(x, rz2), Fp.mul(Fp.mul(y, rz2), rz), #fp(1));
    };

    /// Converts a Jacobi point to its affine `Point` representation,
    /// performing one modular inversion. Returns `#zero` for the point at
    /// infinity.
    public func fromJacobi(a : Jacobi) : Point {
      let (x, y, z) = normalize(a);
      if (z == #fp(0)) return #zero;
      #affine(x, y);
    };

    /// Returns `true` when the Jacobi point lies on the curve. Works
    /// without normalising `Z`.
    public func isValid((x, y, z) : Jacobi) : Bool {
      let x2 = Fp.sqr(x);
      let y2 = Fp.sqr(y);
      let z2 = Fp.sqr(z);
      var z4 = Fp.sqr(z2);
      var t = Fp.mul(z4, a_);
      t := Fp.add(t, x2);
      t := Fp.mul(t, x);
      z4 := Fp.mul(z4, z2);
      z4 := Fp.mul(z4, b_);
      t := Fp.add(t, z4);
      y2 == t;
    };

    /// Returns `true` when `P1` and `P2` represent the same curve point.
    /// Compares without forcing normalisation of either input.
    public func isEqual(P1 : Jacobi, P2 : Jacobi) : Bool {
      let zero1 = isZero(P1);
      let zero2 = isZero(P2);
      if (zero1) return zero2;
      if (zero2) return false;
      let (x1, y1, z1) = P1;
      let (x2, y2, z2) = P2;
      let s1 = Fp.sqr(z1);
      let s2 = Fp.sqr(z2);
      var t1 = Fp.mul(x1, s2);
      var t2 = Fp.mul(x2, s1);
      if (t1 != t2) return false;
      t1 := Fp.mul(y1, s2);
      t2 := Fp.mul(y2, s1);
      t1 := Fp.mul(t1, z2);
      t2 := Fp.mul(t2, z1);
      t1 == t2;
    };

    /// Returns the additive inverse `-P` of a Jacobi point.
    public func neg((x, y, z) : Jacobi) : Jacobi = (x, Fp.neg(y), z);

    /// Doubles the Jacobi point `P` (i.e. returns `P + P`). Uses an
    /// optimised formula when the curve has `a = -3` (prime256v1).
    public func dbl((x, y, z) : Jacobi) : Jacobi {
      if (z == #fp(0)) return zeroJ;

      // Special optimized formula for curves with a=-3 (like prime256v1)
      // Uses complete formulas from https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html

      let x2 = Fp.sqr(x);
      let y2 = Fp.sqr(y);

      // S = 4*x*y^2
      var S = Fp.mul(x, y2);
      S := Fp.add(S, S);
      S := Fp.add(S, S);

      // M = 3*x^2 + a*z^4
      var M = Fp.add(x2, x2);
      M := Fp.add(M, x2); // 3*x^2

      if (a_ != #fp(0)) {
        // For prime256v1, a = -3
        let z4 = Fp.sqr(Fp.sqr(z));
        let az4 = Fp.mul(a_, z4);
        M := Fp.add(M, az4); // 3*x^2 + a*z^4
      };

      // x' = M^2 - 2*S
      var rx = Fp.sqr(M);
      rx := Fp.sub(rx, S);
      rx := Fp.sub(rx, S);

      // y' = M*(S - x') - 8*y^4
      var y4 = Fp.sqr(y2);
      y4 := Fp.add(y4, y4);
      y4 := Fp.add(y4, y4);
      y4 := Fp.add(y4, y4); // 8*y^4

      var ry = Fp.sub(S, rx); // S - x'
      ry := Fp.mul(M, ry); // M*(S - x')
      ry := Fp.sub(ry, y4); // M*(S - x') - 8*y^4

      // z' = 2*y*z
      var rz = Fp.mul(y, z);
      rz := Fp.add(rz, rz);

      return (rx, ry, rz);
    };

    /// Adds two Jacobi points. Handles the point-at-infinity and
    /// equal-input cases by delegating to `dbl` or returning `zeroJ`.
    public func add((px, py, pz) : Jacobi, (qx, qy, qz) : Jacobi) : Jacobi {
      if (pz == #fp(0)) return (qx, qy, qz);
      if (qz == #fp(0)) return (px, py, pz);
      let isPzOne = pz == #fp(1);
      let isQzOne = qz == #fp(1);
      var r = if (isPzOne) #fp(1) else Fp.sqr(pz);
      var U1 = #fp(0);
      var S1 = #fp(0);
      var H = #fp(0);
      if (isQzOne) {
        U1 := px;
        if (isPzOne) {
          H := qx;
        } else {
          H := Fp.mul(qx, r);
        };
        H := Fp.sub(H, U1);
        S1 := py;
      } else {
        S1 := Fp.sqr(qz);
        U1 := Fp.mul(px, S1);
        if (isPzOne) {
          H := qx;
        } else {
          H := Fp.mul(qx, r);
        };
        H := Fp.sub(H, U1);
        S1 := Fp.mul(S1, qz);
        S1 := Fp.mul(S1, py);
      };
      if (isPzOne) {
        r := qy;
      } else {
        r := Fp.mul(r, pz);
        r := Fp.mul(r, qy);
      };
      r := Fp.sub(r, S1);
      if (H == #fp(0)) {
        if (r == #fp(0)) {
          return dbl((px, py, pz));
        } else {
          return zeroJ;
        };
      };
      var rx = #fp(0);
      var ry = #fp(0);
      var rz = #fp(0);
      if (isPzOne) {
        if (isQzOne) {
          rz := H;
        } else {
          rz := Fp.mul(H, qz);
        };
      } else {
        if (isQzOne) {
          rz := Fp.mul(pz, H);
        } else {
          rz := Fp.mul(pz, qz);
          rz := Fp.mul(rz, H);
        };
      };
      var H3 = Fp.sqr(H);
      ry := Fp.sqr(r);
      U1 := Fp.mul(U1, H3);
      H3 := Fp.mul(H3, H);
      ry := Fp.sub(ry, U1);
      ry := Fp.sub(ry, U1);
      rx := Fp.sub(ry, H3);
      U1 := Fp.sub(U1, rx);
      U1 := Fp.mul(U1, r);
      H3 := Fp.mul(H3, S1);
      ry := Fp.sub(U1, H3);
      (rx, ry, rz);
    };

    /// Subtracts the Jacobi point `Q` from `P` (i.e. returns `P + (-Q)`).
    public func sub((px, py, pz) : Jacobi, (qx, qy, qz) : Jacobi) : Jacobi = add((px, py, pz), (qx, Fp.neg(qy), qz));

    // ===== Internal point arithmetic on raw `Nat`s (scalar-mul hot path) =====
    //
    // Coordinates are kept in the curve's working domain: plain residues
    // mod p for secp256k1 (reduced with `reduceSecp`) and Montgomery form
    // for prime256v1 (reduced with `redcP`). This avoids the `#fp` boxing
    // and closure dispatch of the public `Fp` API in the inner loops.
    // A point with `Z == 0` is the point at infinity; a point with
    // `Z == oneN` is affine and takes the cheaper mixed-addition path.

    type JacobiN = (Nat, Nat, Nat);
    let zeroJN : JacobiN = (0, 0, 0);
    let oneN : Nat = if (isP256) oneM else 1;

    func fmul(a : Nat, b : Nat) : Nat = if (isP256) redcP(a * b) else reduceSecp(a * b);
    func fsqr(a : Nat) : Nat = if (isP256) redcP(a * a) else reduceSecp(a * a);
    func fadd(a : Nat, b : Nat) : Nat {
      let s = a + b;
      if (s >= p_) s - p_ else s;
    };
    func fsub(a : Nat, b : Nat) : Nat = if (a >= b) a - b else a + p_ - b;
    func fneg(a : Nat) : Nat = if (a == 0) 0 else p_ - a;
    func toN(a : Nat) : Nat = if (isP256) toMontP(a) else a;
    func fromN(a : Nat) : Nat = if (isP256) fromMontP(a) else a;
    // Inverse in the working domain. In Montgomery form `inv(aR)` is
    // `a^-1 R^-1`, so two `toMontP` steps turn it into `a^-1 R`.
    func finv(a : Nat) : Nat {
      let i = Field.inv_(a, p_);
      if (isP256) toMontP(toMontP(i)) else i;
    };

    func toJacobiN((#fp(x), #fp(y), #fp(z)) : Jacobi) : JacobiN {
      if (z == 0) return zeroJN;
      (toN(x), toN(y), toN(z));
    };

    func fromJacobiN((x, y, z) : JacobiN) : Jacobi {
      if (z == 0) return zeroJ;
      (#fp(fromN(x)), #fp(fromN(y)), #fp(fromN(z)));
    };

    // Point doubling. Both curves have `a = 0` (secp256k1) or `a = -3`
    // (prime256v1); for the latter `M = 3*X^2 + a*Z^4 = 3(X - Z^2)(X + Z^2)`.
    func dblN((x, y, z) : JacobiN) : JacobiN {
      if (z == 0) return zeroJN;
      let y2 = fsqr(y);
      // S = 4*X*Y^2
      var s = fmul(x, y2);
      s := fadd(s, s);
      s := fadd(s, s);
      // M = 3*X^2 + a*Z^4
      let m = if (isP256) {
        let z2 = fsqr(z);
        let t = fmul(fsub(x, z2), fadd(x, z2));
        fadd(fadd(t, t), t);
      } else {
        let x2 = fsqr(x);
        fadd(fadd(x2, x2), x2);
      };
      // X' = M^2 - 2*S
      let rx = fsub(fsub(fsqr(m), s), s);
      // Y' = M*(S - X') - 8*Y^4
      var y4 = fsqr(y2);
      y4 := fadd(y4, y4);
      y4 := fadd(y4, y4);
      y4 := fadd(y4, y4);
      let ry = fsub(fmul(m, fsub(s, rx)), y4);
      // Z' = 2*Y*Z
      let rz = fmul(y, z);
      (rx, ry, fadd(rz, rz));
    };

    // Point addition. When `Q` is affine (`qz == oneN`) the mixed formula
    // saves four field multiplications.
    func addN((px, py, pz) : JacobiN, (qx, qy, qz) : JacobiN) : JacobiN {
      if (pz == 0) return (qx, qy, qz);
      if (qz == 0) return (px, py, pz);
      let pz2 = fsqr(pz);
      let u2 = fmul(qx, pz2);
      let s2 = fmul(qy, fmul(pz, pz2));
      let qAffine = qz == oneN;
      var u1 = px;
      var s1 = py;
      if (not qAffine) {
        let qz2 = fsqr(qz);
        u1 := fmul(px, qz2);
        s1 := fmul(py, fmul(qz, qz2));
      };
      let h = fsub(u2, u1);
      let r = fsub(s2, s1);
      if (h == 0) {
        return if (r == 0) dblN((px, py, pz)) else zeroJN;
      };
      let h2 = fsqr(h);
      let h3 = fmul(h, h2);
      let v = fmul(u1, h2);
      let rx = fsub(fsub(fsub(fsqr(r), h3), v), v);
      let ry = fsub(fmul(r, fsub(v, rx)), fmul(s1, h3));
      let rz = if (qAffine) fmul(pz, h) else fmul(fmul(pz, qz), h);
      (rx, ry, rz);
    };

    // Converts points to affine form (`Z = oneN`) with a single field
    // inversion (Montgomery's trick). No point may be the point at infinity.
    func normalizeAllN(pts : [JacobiN]) : [JacobiN] {
      let n = pts.size();
      let prefix = VarArray.repeat<Nat>(0, n);
      var acc = oneN;
      var i = 0;
      while (i < n) {
        acc := fmul(acc, pts[i].2);
        prefix[i] := acc;
        i += 1;
      };
      var inv = finv(acc);
      let out = VarArray.repeat<JacobiN>(zeroJN, n);
      i := n;
      while (i > 0) {
        i -= 1;
        let (x, y, z) = pts[i];
        let zi = if (i == 0) inv else fmul(inv, prefix[i - 1]);
        if (i > 0) inv := fmul(inv, z);
        let zi2 = fsqr(zi);
        out[i] := (fmul(x, zi2), fmul(y, fmul(zi2, zi)), oneN);
      };
      out.toArray();
    };

    // Window width of the wNAF scalar recoding and the resulting number of
    // precomputed odd multiples, 2^(w-2).
    let WNAF_W = 5;
    let WNAF_SIZE = 8;

    // A wNAF table maps a non-zero odd digit `d` to the point `d * P`.
    type WnafTable = (d : Int) -> JacobiN;

    // Wraps the odd multiples `P, 3P, 5P, ...` together with their negations.
    func arrayTable(pos : [JacobiN]) : WnafTable {
      let neg = pos.map(func((x, y, z) : JacobiN) : JacobiN = (x, fneg(y), z));
      func(d) = if (d > 0) pos[Int.abs(d) / 2] else neg[Int.abs(d) / 2];
    };

    // The odd multiples P, 3P, ..., 15P.
    func oddMultiples(p : JacobiN) : [JacobiN] {
      let p2 = dblN(p);
      let t = VarArray.repeat<JacobiN>(p, WNAF_SIZE);
      var i = 1;
      while (i < WNAF_SIZE) {
        t[i] := addN(t[i - 1], p2);
        i += 1;
      };
      t.toArray();
    };

    // GLV endomorphism (secp256k1 only): `lambda * (x, y) = (beta * x, y)`.
    func lambdaN((x, y, z) : JacobiN) : JacobiN = (fmul(x, glvBeta), y, z);

    // Tables for the terms of `k * P`: on secp256k1 the GLV endomorphism
    // gives the second table for free.
    func tablesFor(p : JacobiN) : [WnafTable] = tablesOf(oddMultiples(p));

    func tablesOf(pos : [JacobiN]) : [WnafTable] {
      if (not hasGLV) return [arrayTable(pos)];
      [arrayTable(pos), arrayTable(pos.map(lambdaN))];
    };

    // wNAF digits matching `tablesFor`: two half-length scalars via the GLV
    // split on secp256k1, one full-length scalar on prime256v1.
    func nafsFor(k : Nat) : [[Int]] {
      if (not hasGLV) return [Binary.toNafWidth(k, WNAF_W)];
      let (a, b) = split(k);
      [Binary.toNafWidth(a, WNAF_W), Binary.toNafWidth(b, WNAF_W)];
    };

    // Evaluates `sum_j naf_j * P_j` with interleaved wNAF (Straus /
    // Shamir's trick): all terms share a single chain of doublings.
    func wnafSum(nafs : [[Int]], tables : [WnafTable]) : JacobiN {
      var len = 0;
      for (naf in nafs.values()) if (naf.size() > len) len := naf.size();
      var acc = zeroJN;
      var i = len;
      while (i > 0) {
        i -= 1;
        acc := dblN(acc);
        var j = 0;
        while (j < nafs.size()) {
          let naf = nafs[j];
          if (i < naf.size()) {
            let d = naf[i];
            if (d != 0) acc := addN(acc, tables[j](d));
          };
          j += 1;
        };
      };
      acc;
    };

    // Tables for the generator, built on first use and kept for the
    // lifetime of this `Curve` instance. They are normalised to affine
    // form, so that every addition from them is a cheaper mixed addition.
    var gTablesCache : ?[WnafTable] = null;
    func gTables() : [WnafTable] {
      switch (gTablesCache) {
        case (?t) t;
        case null {
          let t = tablesOf(normalizeAllN(oddMultiples(toJacobiN(G_))));
          gTablesCache := ?t;
          t;
        };
      };
    };

    /// Returns the normalised affine `(x, y, z)` triple as hex strings.
    /// Intended for debug printing.
    public func hexPoint(p : Jacobi) : (Text, Text, Text) {
      let (x, y, z) = normalize(p);
      (Hex.fromNat(Fp.toNat(x)), Hex.fromNat(Fp.toNat(y)), Hex.fromNat(Fp.toNat(z)));
    };

    /// Returns the normalised affine `(x, y, z)` triple as `Nat` values.
    /// Intended for debug printing.
    public func debugPoint(p : Jacobi) : (Nat, Nat, Nat) {
      let (x, y, z) = normalize(p);
      (Fp.toNat(x), Fp.toNat(y), Fp.toNat(z));
    };

    // Splits `k` into `(a, b)` with `k = a + b * lambda (mod r)` and both
    // halves of roughly 128 bits.
    func split(x_ : Nat) : (Int, Int) {
      assert (hasGLV); // Only valid for secp256k1
      let x = x_ : Int;
      let t = (x * GLV_CONSTANTS.v0) / GLV_CONSTANTS.SHIFT256;
      var b = (x * GLV_CONSTANTS.v1) / GLV_CONSTANTS.SHIFT256;
      let a = x - (t * GLV_CONSTANTS.B00 + b * GLV_CONSTANTS.B10);
      b := -(t * GLV_CONSTANTS.B01 + b * GLV_CONSTANTS.B00);
      (a, b);
    };

    /// Computes `scalar * x` with width-5 wNAF, using the GLV endomorphism
    /// on secp256k1. Returns the point at infinity when the scalar is zero
    /// or `x` is already the point at infinity.
    public func mul(x : Jacobi, #fr(k) : FrElt) : Jacobi {
      if (k == 0 or isZero(x)) return zeroJ;
      fromJacobiN(wnafSum(nafsFor(k), tablesFor(toJacobiN(x))));
    };

    /// Computes `x * G`, the scalar multiple of the curve generator.
    public func mul_base(#fr(k) : FrElt) : Jacobi {
      if (k == 0) return zeroJ;
      fromJacobiN(wnafSum(nafsFor(k), gTables()));
    };

    /// Computes `u1 * G + u2 * q` in a single pass that shares all
    /// doublings between both terms (Shamir's trick). This is the core of
    /// ECDSA verification.
    public func mul_base_add(#fr(u1) : FrElt, q : Jacobi, #fr(u2) : FrElt) : Jacobi {
      if (u2 == 0 or isZero(q)) return mul_base(#fr(u1));
      if (u1 == 0) return mul(q, #fr(u2));
      let nafs = nafsFor(u1).concat(nafsFor(u2));
      let tables = gTables().concat(tablesFor(toJacobiN(q)));
      fromJacobiN(wnafSum(nafs, tables));
    };

    /// Debug-prints a `Point` via `Debug.print`.
    public func putPoint(a : Point) {
      switch (a) {
        case (#zero) {
          Debug.print("0");
        };
        case (#affine(x, y)) {
          Debug.print("(" # Hex.fromNat(Fp.toNat(x)) # ", " # Hex.fromNat(Fp.toNat(y)) # ")");
        };
      };
    };

    /// Debug-prints a `Jacobi` point via `Debug.print`.
    public func putJacobi((x, y, z) : Jacobi) {
      Debug.print("(0x" # Hex.fromNat(Fp.toNat(x)) # ", 0x" # Hex.fromNat(Fp.toNat(y)) # ", 0x" # Hex.fromNat(Fp.toNat(z)) # ")");
    };

    /// Debug-prints a signature `(r, s)` via `Debug.print`.
    public func putSig((x, y) : (FrElt, FrElt)) {
      Debug.print("(0x" # Hex.fromNat(Fr.toNat(x)) # ", 0x" # Hex.fromNat(Fr.toNat(y)) # ")");
    };
  };

  /// Returns a fresh `Curve` for secp256k1.
  public func secp256k1() : Curve = Curve(#secp256k1);
  /// Returns a fresh `Curve` for prime256v1 (NIST P-256).
  public func prime256v1() : Curve = Curve(#prime256v1);

  /// Returns the curve parameters for `kind` (field prime, order,
  /// generator, coefficients `a` / `b`, and the precomputed `(p+1)/4`
  /// exponent used for square roots).
  public func getParams(kind : CurveKind) : CurveParams {
    switch (kind) {
      case (#secp256k1) ({
        p = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f;
        r = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141;
        a = #fp(0);
        b = #fp(7);
        g = (
          #fp(0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798),
          #fp(0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8),
        );
        rHalf = 0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a1;
        pSqrRoot = 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffff0c;
        kind = kind;
      });
      case (#prime256v1) ({
        p = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff;
        r = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551;
        a = #fp(0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc);
        b = #fp(0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b);
        g = (
          #fp(0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296),
          #fp(0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5),
        );
        rHalf = 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a8;
        pSqrRoot = 0x3fffffffc0000000400000000000000000000000400000000000000000000000;
        kind = kind;
      });
    };
  };
};
