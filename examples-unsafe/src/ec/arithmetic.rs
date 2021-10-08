use hacspec_lib::*;

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Jacobian<T: UnsignedIntegerCopy>(pub T, pub T, pub T);

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Affine<T: UnsignedIntegerCopy>(pub T, pub T);

fn jacobian_to_affine<T: UnsignedIntegerCopy>(p: Jacobian<T>) -> Affine<T> {
    let (x, y, z) = (p.0, p.1, p.2);
    let z2 = z.exp(2);
    let z2i = z2.inv(T::default()); // argument is not used
    let z3 = z * z2;
    let z3i = z3.inv(T::default()); // argument is not used
    let x = x * z2i;
    let y = y * z3i;
    Affine(x, y)
}

fn affine_to_jacobian<T: UnsignedIntegerCopy>(p: Affine<T>) -> Jacobian<T> {
    Jacobian(p.0, p.1, T::from_literal(1))
}

fn point_double<T: UnsignedIntegerCopy>(p: Jacobian<T>) -> Jacobian<T> {
    let (x1, y1, z1) = (p.0, p.1, p.2);
    let delta = z1.exp(2);
    let gamma = y1.exp(2);

    let beta = x1 * gamma;

    let alpha_1 = x1 - delta;
    let alpha_2 = x1 + delta;
    let alpha = T::from_literal(3) * (alpha_1 * alpha_2);

    let x3 = alpha.exp(2) - (T::from_literal(8) * beta);

    let z3_ = (y1 + z1).exp(2);
    let z3 = z3_ - (gamma + delta);

    let y3_1 = (T::from_literal(4) * beta) - x3;
    let y3_2 = T::from_literal(8) * (gamma * gamma);
    let y3 = (alpha * y3_1) - y3_2;
    Jacobian(x3, y3, z3)
}

fn is_point_at_infinity<T: UnsignedIntegerCopy>(p: Jacobian<T>) -> bool {
    p.2.equal(T::from_literal(0))
}

fn point_add<T: UnsignedIntegerCopy>(p: Jacobian<T>, q: Jacobian<T>) -> Jacobian<T> {
    if is_point_at_infinity(p) {
        return q;
    }
    if is_point_at_infinity(q) {
        return p;
    }
    let (x1, y1, z1) = (p.0, p.1, p.2);
    let (x2, y2, z2) = (q.0, q.1, q.2);
    let z1z1 = z1.exp(2);
    let z2z2 = z2.exp(2);
    let u1 = x1 * z2z2;
    let u2 = x2 * z1z1;
    let s1 = (y1 * z2) * z2z2;
    let s2 = (y2 * z1) * z1z1;

    if u1.equal(u2) {
        assert!(!s1.equal(s2));
        return Jacobian(T::from_literal(0), T::from_literal(1), T::from_literal(0));
    }

    let h = u2 - u1;
    let i = (T::from_literal(2) * h).exp(2);
    let j = h * i;
    let r = T::from_literal(2) * (s2 - s1);
    let v = u1 * i;

    let x3_1 = T::from_literal(2) * v;
    let x3_2 = r.exp(2) - j;
    let x3 = x3_2 - x3_1;

    let y3_1 = (T::from_literal(2) * s1) * j;
    let y3_2 = r * (v - x3);
    let y3 = y3_2 - y3_1;

    let z3_ = (z1 + z2).exp(2);
    let z3 = (z3_ - (z1z1 + z2z2)) * h;
    Jacobian(x3, y3, z3)
}

#[allow(dead_code)]
fn montgomery_ladder<T: UnsignedIntegerCopy, I: UnsignedIntegerCopy>(
    k: I,
    init: Jacobian<T>,
) -> Jacobian<T> {
    let mut p_working = (
        Jacobian(T::from_literal(0), T::from_literal(1), T::from_literal(0)),
        init,
    );
    for i in 0..T::NUM_BITS {
        if k.get_bit(T::NUM_BITS - 1 - i).equal(I::ONE()) {
            p_working = (p_working.1, p_working.0);
        }
        let xx = point_double(p_working.0);
        let xp1 = point_add(p_working.0, p_working.1);
        if k.get_bit(T::NUM_BITS - 1 - i).equal(I::ONE()) {
            p_working = (xp1, xx);
        } else {
            p_working = (xx, xp1);
        }
    }
    p_working.0
}

fn ltr_mul<T: UnsignedIntegerCopy, I: UnsignedIntegerCopy>(k: I, p: Jacobian<T>) -> Jacobian<T> {
    let mut q = Jacobian(T::from_literal(0), T::from_literal(1), T::from_literal(0));
    for i in 0..T::NUM_BITS {
        q = point_double(q);
        if k.get_bit(T::NUM_BITS - 1 - i).equal(I::ONE()) {
            q = point_add(q, p);
        }
    }
    q
}

pub fn point_mul<T: UnsignedIntegerCopy, I: UnsignedIntegerCopy>(k: I, p: Affine<T>) -> Affine<T> {
    let jac = ltr_mul(k, affine_to_jacobian(p));
    jacobian_to_affine(jac)
}
