////////////////////////////////////////////////////////////////////////////////
// Author: Kareem Waseem
// Course: Digital Verification using SV & UVM
//
// Description: UVM Example
//
////////////////////////////////////////////////////////////////////////////////
package slave_test_pkg;
import slave_env_pkg::*;
import uvm_pkg::*;
import config_pkg::*;
import main_seq_pkg::*;
import reset_seq_pkg::*;
import slave_env_pkg::*;
`include "uvm_macros.svh"

class slave_test extends uvm_test;
  // Do the essentials (factory register & Constructor)
	`uvm_component_utils(slave_test)

	slave_env env;
	slave_config slave_cfg;
	virtual slave_if slave_vif;
	slave_main_seq main_seq;
	slave_reset_seq reset_seq;

	function new (string name = "slave_test", uvm_component parent = null);
		super.new (name, parent);
	endfunction

	function void build_phase (uvm_phase phase);
		super.build_phase (phase);
		env       = slave_env      ::type_id::create("env", this);
		slave_cfg  = slave_config   ::type_id::create("slave_cfg");
		main_seq  = slave_main_seq ::type_id::create("main_seq");
		reset_seq = slave_reset_seq::type_id::create("reset_seq");

		if (!uvm_config_db#(virtual slave_if)::get(this, "", "ifk", slave_cfg.slave_vif))
			`uvm_fatal ("build_phase", "errrrrrrrrrrrrrorrrrrrrrrrrrrrrrrrr");

		uvm_config_db#(slave_config)::set(this, "*", "cfg", slave_cfg);
	endfunction

	task run_phase (uvm_phase phase);
		super.run_phase (phase);
		phase.raise_objection(this);
		`uvm_info ("run_phase", "welcommmmmmmmmmmmmmmmmmmmmmme", UVM_MEDIUM)
		reset_seq.start(env.agt.sqr);
		main_seq.start(env.agt.sqr);
		phase.drop_objection(this);
	endtask

endclass: slave_test
endpackage
