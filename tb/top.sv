////////////////////////////////////////////////////////////////////////////////
// Author: Kareem Waseem
// Course: Digital Verification using SV & UVM
//
// Description: UVM Example
//
////////////////////////////////////////////////////////////////////////////////
import uvm_pkg::*;
import slave_test_pkg::*;
`include "uvm_macros.svh"

module top();
  // Clock generation
	bit clk;
	initial forever #1 clk = !clk;
  // Instantiate the interface and DUT
	slave_if a_if (clk);
	SLAVE dut (a_if.MOSI,a_if.MISO,a_if.SS_n,clk,a_if.rst_n,a_if.rx_data,a_if.rx_valid,a_if.tx_data,a_if.tx_valid);
	golden_model golden (a_if.MOSI,a_if.MISO_golden,a_if.SS_n,clk,a_if.rst_n,a_if.rx_data_golden,a_if.rx_valid_golden,a_if.tx_data,a_if.tx_valid);
	bind SLAVE sva sva_inst(clk,a_if.MOSI,a_if.rst_n,a_if.SS_n,a_if.tx_valid,a_if.tx_data,a_if.rx_data,a_if.rx_valid,a_if.MISO);
  	initial begin
		uvm_config_db #(virtual slave_if)::set(null, "uvm_test_top", "ifk", a_if);
		run_test("slave_test");
	end
endmodule
