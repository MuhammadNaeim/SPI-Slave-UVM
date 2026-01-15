package agent_pkg;
    import uvm_pkg::*;
    import seq_item_pkg::*;
    import driver_pkg::*;
    import sequencer_pkg::*;
    import monitor_pkg::*;
    import config_pkg::*;
	`include "uvm_macros.svh"

    class slave_agent extends uvm_agent;
        `uvm_component_utils(slave_agent)
        slave_sequencer sqr;
        slave_driver drv;
        slave_monitor mon;
        slave_config slave_cfg;
        uvm_analysis_port #(slave_seq_item) agt_ap;

        function new(string name = "slave_agent", uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            if(!uvm_config_db#(slave_config)::get(this, "", "cfg", slave_cfg))
            `uvm_fatal("build_phase", "errrrrrorrrrrrr")

            sqr = slave_sequencer::type_id::create("sqr", this);
            drv = slave_driver   ::type_id::create("drv", this);
            mon = slave_monitor  ::type_id::create("mon", this);
            agt_ap = new("agt_ap", this);
        endfunction

        function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            drv.slave_vif = slave_cfg.slave_vif;
            mon.slave_vif = slave_cfg.slave_vif;
            drv.seq_item_port.connect(sqr.seq_item_export);
            mon.mon_ap.connect(agt_ap);
        endfunction
    endclass
endpackage
