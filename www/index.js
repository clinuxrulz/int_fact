import * as wasm from "int_fact";

let txtCnf = document.getElementById("txtCnf");
let btnSolve = document.getElementById("btnSolve");

btnSolve.addEventListener("click", function() {
    let r = wasm.solve(txtCnf.value);
    alert(r);
});

