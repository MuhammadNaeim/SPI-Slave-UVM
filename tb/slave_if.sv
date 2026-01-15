interface slave_if(clk);
    input clk;
    logic MOSI, rst_n, SS_n, tx_valid;
    logic [7:0] tx_data;
    logic [9:0] rx_data;
    logic       rx_valid, MISO;
    logic [9:0] rx_data_golden;
    logic       rx_valid_golden, MISO_golden;
endinterface
