module SLAVE (MOSI,MISO,SS_n,clk,rst_n,rx_data,rx_valid,tx_data,tx_valid);

    localparam IDLE      = 3'b000;
    localparam WRITE     = 3'b001;
    localparam CHK_CMD   = 3'b010;
    localparam READ_ADD  = 3'b011;
    localparam READ_DATA = 3'b100;

    input            MOSI, clk, rst_n, SS_n, tx_valid;
    input      [7:0] tx_data;
    output reg [9:0] rx_data;
    output reg       rx_valid, MISO;

    reg [3:0] counter;
    reg       received_address;

    reg [2:0] cs, ns;

    always @(posedge clk) begin
        if (~rst_n) begin
            cs <= IDLE;
        end
        else begin
            cs <= ns;
        end
    end

    always @(*) begin
        case (cs)
            IDLE : begin
                if (SS_n)
                    ns = IDLE;
                else
                    ns = CHK_CMD;
            end
            CHK_CMD : begin
                if (SS_n)
                    ns = IDLE;
                else begin
                    if (~MOSI)
                        ns = WRITE;
                    else begin
                        if (~received_address)//////not
                            ns = READ_ADD;
                        else
                            ns = READ_DATA;
                    end
                end
            end
            WRITE : begin
                if (SS_n)
                    ns = IDLE;
                else
                    ns = WRITE;
            end
            READ_ADD : begin
                if (SS_n)
                    ns = IDLE;
                else
                    ns = READ_ADD;
            end
            READ_DATA : begin
                if (SS_n)
                    ns = IDLE;
                else
                    ns = READ_DATA;
            end
        endcase
    end

    always @(posedge clk) begin
        if (~rst_n) begin
            rx_data <= 0;
            rx_valid <= 0;
            received_address <= 0;
            MISO <= 0;
            counter <= 0; /////////rest
        end
        else begin
            case (cs)
                IDLE : begin
                    rx_valid <= 0;
                end
                CHK_CMD : begin
                    //////// read data counter = 8
                    if (!SS_n && received_address) counter <= 8;
                    else counter <= 10;
                end
                WRITE : begin
                    if (counter > 0) begin
                        rx_data[counter-1] <= MOSI;
                        counter <= counter - 1;
                    end
                    else begin
                        rx_valid <= 1;
                    end
                end
                READ_ADD : begin
                    if (counter > 0) begin
                        rx_data[counter-1] <= MOSI;
                        counter <= counter - 1;
                    end
                    else begin
                        rx_valid <= 1;
                        received_address <= 1;
                    end
                end
                READ_DATA : begin
                    if (tx_valid) begin
                        rx_valid <= 0;
                        if (counter > 0) begin
                            MISO <= tx_data[counter-1];
                            counter <= counter - 1;
                        end
                        else begin
                            received_address <= 0;
                        end
                    end
                    else begin
                        if (counter > 0) begin
                            rx_data[counter-1] <= MOSI;
                            counter <= counter - 1;
                        end
                        else begin
                            rx_valid <= 1;
                            counter  <= 10; //////10
                        end
                    end
                end
            endcase
        end
    end


    `ifdef SIM


    property idle_chk_p;
        @(posedge clk) disable iff (!rst_n) (cs == IDLE) |=> cs == CHK_CMD [-> 1]
    endproperty
    idle_chk_a: assert property (idle_chk_p);
    idle_chk_c: cover  property (idle_chk_p);

    property chk_wr_p;
        @(posedge clk) disable iff (!rst_n) (cs == CHK_CMD) |=> cs == (WRITE || READ_ADD || READ_DATA) [-> 1]
    endproperty
    chk_wr_a: assert property (chk_wr_p);
    chk_wr_c: cover  property (chk_wr_p);

    property wr_idle_p;
        @(posedge clk) disable iff (!rst_n) (cs == WRITE) |=> cs == (IDLE) [-> 1]
    endproperty
    wr_idle_a: assert property (wr_idle_p);
    wr_idle_c: cover  property (wr_idle_p);

    property rd_add_idle_p;
        @(posedge clk) disable iff (!rst_n) (cs == READ_ADD) |=> cs == (IDLE) [-> 1]
    endproperty
    rd_add_idle_a: assert property (rd_add_idle_p);
    rd_add_idle_c: cover  property (rd_add_idle_p);

    property rd_data_idle_p;
        @(posedge clk) disable iff (!rst_n) (cs == READ_DATA) |=> cs == (IDLE) [-> 1]
    endproperty
    rd_data_idle_a: assert property (rd_data_idle_p);
    rd_data_idle_c: cover  property (rd_data_idle_p);


    `endif

    endmodule
