use std::io::{stdin, stdout, Write};
use std::time::{Duration, Instant};
use anyhow::Error;
use bitvector::BitVector;
use itertools::Itertools;
use rug::Integer;
use rug::ops::Pow;

const MAX_DURATION: Duration = Duration::from_secs(120);

fn run() -> Result<(), Error> {
    let n: Integer = input("Enter a number to factor: ")?.parse()?;

    brute_force(&n)?;
    println!();

    pollards_rho(&n)?;
    println!();

    dixons(&n)?;

    Ok(())
}

fn brute_force(n: &Integer) -> Result<(), Error> {
    println!("Brute Force:");

    let start = Instant::now();

    let mut i: Integer = 2.into();
    let i_max = n.clone().sqrt();

    while i <= i_max {
        if start.elapsed() > MAX_DURATION {
            println!("FAILED: Timeout");
            return Ok(());
        }

        if n.is_divisible(&i) {
            println!("SUCCESS: Found factor {}", i);
            println!("It took {:?}", start.elapsed());
            return Ok(());
        }

        i += 1;
    }

    println!("FAILED: No factor found");
    Ok(())
}

fn pollards_rho(n: &Integer) -> Result<(), Error> {
    println!("Pollard's Rho:");

    let start = Instant::now();

    let mut a: Integer = 2.into();
    let mut b: Integer = 2.into();

    let mut k = 1;

    let f = move |x: Integer| -> Integer {
        Integer::modulo(x.square() + k, n)
    };

    loop {
        a = f(a);
        b = f(f(b));

        if start.elapsed() > MAX_DURATION {
            println!("FAILED: Timeout");
            return Ok(());
        }

        let d = Integer::from(&a - &b).abs().gcd(n);

        if &d == n {
            println!("Iteration {} Failure", k);
            if k == 3 {
                println!("FAILURE: All 3 iterations failed")
            } else {
                k += 1;
            }
        } else if d != 1 {
            println!("a={}, b={}", a, b);
            println!("SUCCESS: Found factor {}", d);
            println!("It took {:?}", start.elapsed());
            return Ok(());
        }
    }
}


#[derive(Debug, Clone)]
struct GoodEquation {
    x: Integer,
    eq_mod_2: BitVector,
    eq: Vec<u32>
}

fn new_good_equation(k: &mut i32, n: &Integer, fb_size: usize, fb: &[Integer], eqs: &mut Vec<GoodEquation>, start: Instant) -> bool {
    loop {
        if start.elapsed() > MAX_DURATION {
            println!("FAILED: Timeout");
            return false;
        }

        let x: Integer = Integer::modulo((Integer::from(*k) * n).sqrt() + 1, n);
        *k += 1;

        // number to factor - x^2 mod n
        let mut xf = x.clone().square().modulo(n);

        let mut bv = BitVector::new(fb_size);
        let mut nv: Vec<u32> = Vec::with_capacity(fb_size);

        for (i, f) in fb.iter().enumerate() {
            let n;
            (xf, n) = xf.remove_factor(f);
            nv.push(n);
            if n % 2 != 0 {
                bv.insert(i);
            }
        }

        // If we get to 1 we have removed all the factors!
        if xf == 1 {
            let eq = GoodEquation {
                x,
                eq_mod_2: bv,
                eq: nv
            };

            println!("{:?}", eq);

            eqs.push(eq);
            return true;
        }
    }
}

fn dixons(n: &Integer) -> Result<(), Error> {
    println!("Dixon's Algorithm:");

    let fb_size: usize = input("Size of factor base: ")?.trim().parse()?;

    let start = Instant::now();

    // Generate factor base
    let mut fb: Vec<Integer> = Vec::with_capacity(fb_size);
    let mut x = 2;
    while fb.len() < fb_size {
        if fb.iter().any(|f| x % f.clone() == 0) {
            x += 1;
        } else {
            fb.push(x.into());
        }
    }
    println!("Factor base generated: {:?}", fb);

    for tries in 0..3 {
        // Generate good equations
        let mut eqs: Vec<GoodEquation> = Vec::with_capacity(fb_size + 1);
        let mut k = 1;

        for _ in 0..fb_size + 1 {
            if !new_good_equation(&mut k, n, fb_size, &fb, &mut eqs, start) { return Ok(()) };
        }

        // Iterate through all combinations
        let zero = BitVector::new(fb_size);
        let mut bv = BitVector::new(fb_size);
        for c_len in 1..=eqs.len() {
            for c in eqs.iter().cloned().combinations(c_len) {
                if start.elapsed() > MAX_DURATION {
                    println!("FAILED: Timeout");
                    return Ok(());
                }

                bv.clear();
                for eq in &c {
                    bv.difference_d_inplace(&eq.eq_mod_2);
                }

                // ALL EXPONENTS ARE EVEN
                if bv == zero {
                    let mut lhs: Integer = 1.into();

                    let mut rhs_factors = vec![0u32; fb_size];

                    for eq in c {
                        lhs *= eq.x;

                        for (i, k) in eq.eq.iter().enumerate() {
                            rhs_factors[i] += k;
                        }
                    }

                    let mut rhs: Integer = 1.into();

                    for (i, k) in rhs_factors.iter().enumerate() {
                        if k % 2 != 0 {
                            panic!("Invalid even exponent!!!");
                        }
                        rhs *= fb[i].clone().pow(k / 2);
                    }

                    let f = (lhs - rhs).abs().gcd(n);

                    if f != 1 && &f != n {
                        println!("SUCCESS: Found factor {}", f);
                        println!("It took {:?}", start.elapsed());
                        return Ok(());
                    }
                }
            }
        }

        println!("Attempt {} failed", tries + 1);
    }

    println!("FAILURE: All 3 iterations failed");
    Ok(())
}

fn main() {
    match run() {
        Ok(_) => {}
        Err(e) => {
            println!("Error: {}", e)
        }
    }
}

fn input(prompt: &str) -> Result<String, Error> {
    let mut input = String::new();
    print!("{}", prompt);
    stdout().flush()?;
    stdin().read_line(&mut input)?;
    Ok(input)
}