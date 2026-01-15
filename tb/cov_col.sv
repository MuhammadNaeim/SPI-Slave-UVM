package cov_col_pkg;
    import uvm_pkg::*;
    import seq_item_pkg::*;
    import shared_pkg::*;
    `include "uvm_macros.svh"
    class slave_coverage extends uvm_component;
        `uvm_component_utils(slave_coverage)
        uvm_analysis_export #(slave_seq_item) cov_export;
        uvm_tlm_analysis_fifo #(slave_seq_item) cov_fifo;
        slave_seq_item seq_item_cov;

        ///////////////// cover group /////////////////
        covergroup cov_gp;
            rx_data_cp : coverpoint seq_item_cov.rx_data[9:8];
            rx_trans_cp: coverpoint seq_item_cov.rx_data[9:8] {
                bins t_00_00 = (2'b00 => 2'b00);
                bins t_00_01 = (2'b00 => 2'b01);
                bins t_00_10 = (2'b00 => 2'b10);
                bins t_01_00 = (2'b01 => 2'b00);
                bins t_01_01 = (2'b01 => 2'b01);
                bins t_01_11 = (2'b01 => 2'b11);
                bins t_10_00 = (2'b10 => 2'b00);
                bins t_10_11 = (2'b10 => 2'b11);
                bins t_11_00 = (2'b11 => 2'b00);
                bins t_11_01 = (2'b11 => 2'b01);
                bins t_11_11 = (2'b11 => 2'b11);
                }
            ss_n_cp : coverpoint seq_item_cov.SS_n {
                bins normal_tr   = (1 => 0[*13] => 1);
                bins extended_tr = (1 => 0[*23] => 1);
            }
            mosi_cp : coverpoint seq_item_cov.MOSI {
                bins write_addr = (0 => 0 => 0);
                bins write_data = (0 => 0 => 1);
                bins read_addr  = (1 => 1 => 0);
                bins read_data  = (1 => 1 => 1);
            }
            patterns_by_protocol : cross ss_n_cp, mosi_cp {
                ignore_bins wr_addr = binsof(ss_n_cp.extended_tr) && binsof(mosi_cp.write_addr);
                ignore_bins wr_data = binsof(ss_n_cp.extended_tr) && binsof(mosi_cp.write_data);
                ignore_bins rd_addr = binsof(ss_n_cp.extended_tr) && binsof(mosi_cp.read_addr);
            }

        endgroup

        function new(string name = "slave_coverage", uvm_component parent = null);
            super.new(name, parent);
            // covergroups inst.
            cov_gp = new;
        endfunction

        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            cov_export = new("cov_export", this);
            cov_fifo = new("cov_info", this);
        endfunction

        function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            cov_export.connect(cov_fifo.analysis_export);
        endfunction

        task run_phase(uvm_phase phase);
            super.run_phase(phase);
            forever begin
            cov_fifo.get(seq_item_cov);
            cov_gp.sample();
            end
        endtask
    endclass
endpackage
