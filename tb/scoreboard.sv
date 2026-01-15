package scoreboard_pkg;
    import uvm_pkg::*;
    import seq_item_pkg::*;
    import shared_pkg::*;
    `include "uvm_macros.svh"
    class slave_scoreboard extends uvm_scoreboard;
        `uvm_component_utils(slave_scoreboard)
        uvm_analysis_export #(slave_seq_item) sb_export;
        uvm_tlm_analysis_fifo #(slave_seq_item) sb_fifo;
        slave_seq_item seq_item_sb;

        function new(string name = "slave_scoreboard", uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            sb_export = new("sb_export", this);
            sb_fifo   = new("sb_fifo",   this);
        endfunction

        function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            sb_export.connect(sb_fifo.analysis_export);
        endfunction

        task run_phase(uvm_phase phase);
            super.run_phase(phase);
            forever begin
            sb_fifo.get(seq_item_sb);
            if (seq_item_sb.MISO_golden !== seq_item_sb.MISO) begin
                `uvm_error("run_phase", $sformatf("errrrrrrrrrrorrrrrrrrr"))
                error++;
            end
            else begin
                `uvm_info("run_phase", $sformatf("corrrrrecccccccccccccct"), UVM_HIGH)
                correct++;
            end
            end
        endtask

    endclass
endpackage
