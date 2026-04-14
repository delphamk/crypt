use rustsat::instances::SatInstance;
use rustsat::solvers::{Solve, SolverResult};
use rustsat_minisat::core::Minisat;

fn main() {
    let mut instance: SatInstance = SatInstance::new();

    // 1. Define our variables
    let alice = instance.new_lit(); // True if Alice is in the office
    let bob = instance.new_lit(); // True if Bob is in the office

    // 2. Constraint: "At least one person must work" (Alice OR Bob)
    instance.add_binary(alice, bob);

    // 3. Constraint: "They cannot both be there" (NOT Alice OR NOT Bob)
    // This is the classic "At Most One" constraint.
    // If Alice is there (!alice is false), Bob MUST NOT be there (bob becomes false).
    instance.add_binary(!alice, !bob);

    // 4. Constraint: "Bob is feeling sick and cannot come in"
    // We force Bob to be False.
    instance.add_unit(!bob);

    // if alice is also not there, it cannot be solved.
    // instance.add_unit(!alice);

    // --- Solver Logic ---
    let mut solver = Minisat::default();
    let (cnf, _) = instance.into_cnf();
    solver.add_cnf(cnf).unwrap();

    if let SolverResult::Sat = solver.solve().unwrap() {
        let sol = solver.full_solution().unwrap();

        // TernaryVal::Pos = True, TernaryVal::Neg = False
        println!("Can we solve the schedule? YES");
        println!("Alice working: {:?}", sol[alice.var()]);
        println!("Bob working: {:?}", sol[bob.var()]);
    } else {
        println!("No valid schedule found!");
    }
}
