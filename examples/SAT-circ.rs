#[derive(Debug, Clone, Copy)]
enum GateType {
    And,
    Or,
    Not,
    Xor,
}

#[derive(Debug, Clone, Copy)]
struct Gate {
    gate_type: GateType,
    inputs: (usize, Option<usize>), // Indices of input wires
    output: usize,                  // Index of output wire
}

struct BooleanCircuit {
    num_wires: usize,
    gates: Vec<Gate>,
    public_output_wire: usize,
}

impl BooleanCircuit {
    /// Evaluates the circuit given a witness (assignment for all input wires).
    fn verify(&self, witness: &[bool]) -> bool {
        // Wire values initialized with the witness for input wires
        let mut wires = vec![false; self.num_wires];
        for (i, &val) in witness.iter().enumerate() {
            wires[i] = val;
        }

        // Process flattened gates in order
        for gate in &self.gates {
            let val1 = wires[gate.inputs.0];
            wires[gate.output] = match gate.gate_type {
                GateType::And => val1 && wires[gate.inputs.1.unwrap()],
                GateType::Or => val1 || wires[gate.inputs.1.unwrap()],
                GateType::Xor => val1 ^ wires[gate.inputs.1.unwrap()],
                GateType::Not => !val1,
            };
        }

        // The circuit is satisfied if the final output wire is TRUE
        wires[self.public_output_wire]
    }
}

fn main() {
    /*
       PROBLEM: Is there an assignment for A, B, C such that:
       (A AND B) XOR (NOT C) == TRUE
    */

    // 1. Define Wires: 0:A, 1:B, 2:C, 3:temp_and, 4:temp_not, 5:final_out
    let circuit = BooleanCircuit {
        num_wires: 6,
        public_output_wire: 5,
        gates: vec![
            Gate {
                gate_type: GateType::And,
                inputs: (0, Some(1)),
                output: 3,
            }, // wire3 = A & B
            Gate {
                gate_type: GateType::Not,
                inputs: (2, None),
                output: 4,
            }, // wire4 = !C
            Gate {
                gate_type: GateType::Xor,
                inputs: (3, Some(4)),
                output: 5,
            }, // wire5 = wire3 ^ wire4
        ],
    };

    // 2. Define a Witness (Potential Solution)
    // Try: A=True, B=True, C=True
    // Calculation: (T & T) ^ (!T) => T ^ F = True
    let witness = vec![true, true, true, false, false, false];

    // 3. Verify the SAT problem
    let is_satisfied = circuit.verify(&witness);

    println!("--- Circ-SAT Solver ---");
    println!("Witness: {:?}", &witness[0..3]); // Show only primary inputs
    println!("Circuit satisfied: {}", is_satisfied);
}
