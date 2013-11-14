uses math;
const  
    Height = 10;
    HalfMovesDescrease = 0;
    SearchDepth = 6; {Глубина работы ABP/число полуходов}
    Width = 9;
    MateValue = 100000;
    PatValue = 0;
    None = 'N';
    Rock = 'R';
    Horse = 'H';
    Elephant = 'E';
    Advisor = 'A';
    General = 'G';
    Pawn = 'S';
    Canon = 'C';
type
    Coordinate = record 
            x:integer;
            y:char;
    end;
    
    Color_t = (White,Black);
    Figure_t = char;
    
    Move_t = record 
        kind : Figure_t;
        from,next : Coordinate;
    end;
    
    Figure = record 
        kind:Figure_t;
        color:Color_t;
    end;
    FigureInfo = record 
        kind:Figure_t;
        position:Coordinate;
    end;


    Table_t = array [0..9,'a'..'i'] of Figure;
    {HashList будет использоваься для хранения оптимизации сравнения двух таблиц для нахождения 4ех повторений позиций.}
    PHashList = ^HashList;
    HashList = record 
        value:int64;
        table:Table_t;
        count:integer;
        next:PHashList;
    end;
    {Будет использоваться для генерации всех ходов и проверки шаха}
    FigureList = array [1..16] of FigureInfo;
    MoveArray = array[0..200] of Move_t;
    {Для проверки мата}
    MovesList = record 
        moves:MoveArray;
        length:integer;
    end;
    {Главная структура игры.}
    PMoveFunction = ^MoveFunction;
    PMoveHandler = ^MoveHandler;
    Game_t = record
        table:Table_t;
        turn:Color_t;
        PlayerOne,PlayerTwo:PMoveFunction;
        hashes,tail:PHashList;
        OnMoveRead : PMoveHandler;
    end;
    MoveHandler = function(var game:Game_t):Move_t;
    MoveFunction = function(var game:Game_t; depth:integer):boolean;

    function FigureCost(fig:FigureInfo; var game:Game_t):integer;
    begin
        case fig.kind of 
            Elephant, Advisor : FigureCost := 16;
            Horse : FigureCost := 32;
            Canon : FigureCost := 36;
            Rock : FigureCost := 72;
            None: FigureCost := 0;
            General: FigureCost := 0;
            Pawn: begin
                if (fig.position.x in [5..9]) and (game.turn = White) or (fig.position.x in [0..4]) and (game.turn = Black) then
                    FigureCost := 16
                else
                    FigureCost := 8;
            end;
        end;
    end;
    function FigureCostMove(move:Move_t; var game:Game_t):integer;
    begin
   //     writeln('/b/:',move.next.x,move.next.y);
        case game.table[move.next.x,move.next.y].kind of 
            Elephant, Advisor : FigureCostMove := 16;
            Horse : FigureCostMove := 32;
            Canon : FigureCostMove := 36;
            Rock : FigureCostMove := 72;
            None: FigureCostMove := 0;
            General: FigureCostMove := 0;
            Pawn: begin
                if (move.next.x in [5..9]) and (game.turn = White) or (move.next.x in [0..4]) and (game.turn = Black) then
                    FigureCostMove := 16
                else
                    FigureCostMove := 8;
            end;
        end;
    end;
    procedure MakeMove(var game:Game_t; var move:Move_t);
    begin
        game.table[move.next.x,move.next.y] := game.table[move.from.x,move.from.y];
        game.table[move.from.x,move.from.y].kind := None;
    end;

    function RandomCoordinate(var game:Game_t; fromx,nextx:integer; _fromy,_nexty:char):Coordinate;
    var
        fromy,nexty:integer;
        res:Coordinate;
    begin
        fromy := ord(_fromy) - ord('a');
        nexty := ord(_nexty) - ord('a');
        if(fromx >= nextx) then 
            res.x := fromx
        else begin
            res.x := fromx + (random(nextx - fromx + 1));
        end;
        if(fromy >= nexty) then 
            res.y := _fromy
        else begin
            res.y := chr(ord('a') + fromy + random(nexty - fromy + 1));
        end;
        RandomCoordinate := res;
    end;
    {Функция рассчета Хэша от таблицы.} {$I-}
    function HashTable(var g:Game_t):int64;
    var
        i,fix:integer;
        h:int64;
        j:char;
    begin
        h := 0; 
        for i := 0 to 9 do begin
            for j := 'a' to 'j' do begin
                if g.table[i,j].kind <> None then fix := 1 + ord(g.table[i,j].color)
                else fix := 0;
                h := h + ((ord(g.table[i,j].kind )+i) shl (fix xor (ord(j) * i)));
            end;
        end;
        HashTable := h + ord(g.turn);
    end;{$I+}
    {Функция генерации хэш-узла для хэш-списка}
    function CreateHashNode(var g:Game_t;hash:int64):PHashList;
    var
        ptr:PHashList;
    begin
        new(ptr);
        ptr^.next := nil;
        ptr^.value := hash;
        ptr^.count := 1;
        ptr^.table := g.table;
        CreateHashNode := ptr;
    end;
    {функция вставки/инкрементирования счетчика для хэш-списка от таблиц, возвращает число повторений текущей позиции}
    function UpdateHash(var g:Game_t):integer;
    var
        iter:PHashList;
        hash:int64;
        function CompareTable(var a,b:Table_t):boolean; {тк хэш-функция не идеальна, то необходима проверка на коллизии, несмотря на ничтожную вероятность этого при выборе хорошей функции}
        var
            j:char;
            i:integer;
        begin
            for i := 0 to Height-1 do begin
                for j:= 'a' to 'i' do begin {при сравнении таблиц необходимо учитывать, что позиции с .kind = None могут иметь разный цвет}
                    if(a[i,j].kind <> b[i,j].kind) or ((a[i,j].kind <> None) and (b[i,j].kind<>None) and (a[i,j].color <> b[i,j].color)) then begin
                        CompareTable := false;
                        exit;
                    end;
                end;
            end;
            CompareTable := true;
        end;
    begin
        iter := g.hashes;
        hash := HashTable(g);
        while iter <> NIL do begin
            if(iter^.value = hash) then begin
                if(CompareTable(g.table,iter^.table))then begin
                    inc(iter^.count);
                    UpdateHash := iter^.count;
                    exit;
                end;
            end;
            iter := iter^.next;
        end;
        iter := CreateHashNode(g,hash);
        if(g.hashes = NIL) then begin
            g.hashes := iter;
            g.tail := iter;
        end else begin
            g.tail^.next := iter;
            g.tail := iter;
        end;
        UpdateHash := 1;
    end;
    {Очистка хэш-листа}
    procedure ResetHashes(var g:Game_t);
    var
        ptr,tmp:PHashList;
    begin
        ptr := g.hashes;
        while ptr <> nil do begin
            tmp := ptr;
            ptr := ptr^.next;
            dispose(tmp);
        end;
        g.hashes := nil;
    end;
    {Добавление элемента в конец списка фигур}
    procedure PushToList(var fList:FigureList; const f:Figure_t; const c:Coordinate; const x:integer);
    begin
        fList[x].kind := f;
        fList[x].position := c;
    end;
    {Функция взятия всех фигур, что еще живы.}
    function GetEnemyFigures(var g:Game_t):FigureList;
    var
        count,i:integer;
        j:char;
        list:FigureList;
        c:Coordinate;
    begin
        count := 0;
        for i := 0 to 9 do begin
            for j:= 'a' to 'i' do begin
              //  writeln(count);
                if (g.table[i,j].color <> g.turn) and (g.table[i,j].kind <> None) then begin
                    count := count +1;
                    c.x := i; c.y := j;
                    PushToList(list,g.table[i,j].kind,c,count);
                end;
            end;
        end;
        GetEnemyFigures := list;
    end;
    procedure ChangeTurn(var game:Game_t);
    begin
        game.turn := Color_t(1 - ord(game.turn));
    end;
    {Тк для каждой стороны своя нумерация строк, то эта функция "чинит" нумерацию относительно белых}
    function fixXCoordinates(i:integer;c:Color_t):integer;
    begin
        if c = White then 
            fixXCoordinates := i
        else 
            fixXCoordinates := Height - i - 1;
    end; 
    {Тк для каждой стороны своя нумерация строк, то эта функция "чинит" нумерацию относительно белых}
    function fixYCoordinates(j:char;c:Color_t):char;
    begin
        if c = White then 
            fixYCoordinates := j
        else 
            fixYCoordinates := chr(Width - ord(j) + 2 * ord('a') - 1);
    end; 
    {Великая и ужасная китайская нотация. Алгоритм ее обработкти:
        - считывание
        - восстановление из номера вертикали - y-индекс
        - нахождение x-индекса фигуры по вертикали
        - обработка x и y индексов клетки, куда делается ход в зависимости от фигуры}
    function ReadAndProccessChineeseNotation(var game:Game_t):Move_t;
    var 
        i,offset:integer;
        y,offsetChr,offsetTy:char;
        move:Move_t;
        searchTy:char = '=';
    begin
        read(move.kind);
        read(y);
        if( y = '^' ) or ( y = 'v' ) then begin
            searchTy := y;
            read(y);
        end;
        y := fixYCoordinates(chr(ord(y) - ord('1') + ord('a')),game.turn);
        read(offsetTy);
        if(not (offsetTy in ['+','-','='])) then begin
            move.kind := None;
            readln;
            ReadAndProccessChineeseNotation := move;
            exit;
        end;
        readln(offsetChr);
        move.from.y := y;
        offset := ord(offsetChr) - ord('0');
        move.from.x := -1;
        {поиск фигуры, если ход белых и требуется нижняя фигура или черные и верхняя,то идем снизу в верх, если нет указания на нижний/верхний, то проверка на единственность фигуры}
        if(game.turn = White) and (searchTy = 'v') or (game.turn = Black) and (searchTy = '^') then begin 
            for i := 0 to Height - 1 do begin
                if (game.table[i,y].kind = move.kind) and (game.table[i,y].color = game.turn) then begin
                    if searchTy = '@' then begin
                        writeln('Two figures at 1 line. Incorrect.');
                        move.kind := None;
                        ReadAndProccessChineeseNotation := move;
                        exit;
                    end;
                    move.from.x := i;
                    if(searchTy = '^') or (searchTy = 'v') then begin
                        break;
                    end;
                    searchTy := '@';
                end; 
            end;
        end else begin
            for i := Height -1  downto 0 do begin
                if (game.table[i,y].kind = move.kind) and (game.table[i,y].color = game.turn) then begin
                    if searchTy = '@' then begin
                        writeln('Two figures at 1 line. Incorrect.');
                        move.kind := None;
                        ReadAndProccessChineeseNotation := move;
                        exit;
                    end;
                    move.from.x := i;
                    if(searchTy = '^') or (searchTy = 'v') then begin
                        break;
                    end;
                    searchTy := '@';
                end; 
            end
        end;
        if(move.from.x = -1) then begin
            move.kind := None;
            ReadAndProccessChineeseNotation := move;
            exit;
        end;
        {Фикс оффсета, по правде говоря, не очень удобно это, но мне лень это менять}
        if(offsetTy = '=') then
            dec(offset);
        if(game.turn = Black) then
            offset := -offset;
        if (offsetTy = '=') and (game.turn = Black) then
            offset := Width - 1 + offset;
        if not (move.kind in [Rock,Canon,Pawn,Horse,Elephant,General,Advisor]) then begin
            move.kind := None;
            ReadAndProccessChineeseNotation := move;
            exit;
        end;
        {обработка в завимости от типа фигуры}
        case move.kind of
            Pawn,General: begin
                move.next := move.from;
                if (offsetTy = '+') then begin
                    inc(move.next.x,offset);
                end else if(offsetTy = '-') then begin
                    dec(move.next.x,offset);
                end else begin
                    move.next.y := chr(ord('a') + offset);
                end;
            end;
            Elephant: begin
                move.next := move.from;
                if (offsetTy = '+') then begin
                    if(game.turn = White) then
                        inc(move.next.x,2)
                    else
                        dec(move.next.x,2);
                end else if(offsetTy = '-') then begin
                    if(game.turn = White) then
                        dec(move.next.x,2)
                    else
                        inc(move.next.x,2);
                end else begin
                    move.kind := None;
                    ReadAndProccessChineeseNotation := move;
                    exit;
                end;
                if(game.turn = Black) then 
                    offset := Width + offset
                else 
                    dec(offset);
                move.next.y := chr(ord('a') +offset);
            end;

            Advisor: begin
                move.next := move.from;
                if (offsetTy = '+') then begin
                    if(game.turn = White) then
                        inc(move.next.x)
                    else
                        dec(move.next.x);
                end else if(offsetTy = '-') then begin
                    if(game.turn = White) then
                        dec(move.next.x)
                    else
                        inc(move.next.x);
                end else begin
                    move.kind := None;
                    ReadAndProccessChineeseNotation := move;
                    exit;
                end;
                if(game.turn = Black) then 
                    offset := Width + offset
                else 
                    dec(offset);
                move.next.y := chr(ord('a') + offset);
            end;
            Rock,Canon: begin
                move.next := move.from;
                if (offsetTy = '=') then begin
                    move.next.y := chr(ord('a') + offset);
                end else if offsetTy = '+' then begin
                    inc(move.next.x,offset);
                end else begin
                    dec(move.next.x,offset);
                end;
            end;
            Horse: begin
                move.next := move.from;
            //    write(offset,' ');
                if(game.turn = Black) then 
                    offset := Width  + offset
                else 
                    dec(offset);
              //  writeln(offset);
                if(offsetTy = '=') then begin
                    move.kind := None;
                    ReadAndProccessChineeseNotation := move;
                    exit;
                end;
                move.next.y := chr(ord('a') + offset);
                if(offsetTy = '-') then begin
                    if abs((offset - ord(move.from.y) + ord('a'))) = 1 then begin
                        if(game.turn = White) then begin
                            dec(move.next.x,2);
                        end else begin
                            inc(move.next.x,2);
                        end;
                    end else if (abs(offset - ord(move.from.y) + ord('a')) = 2) then begin
                        if(game.turn = White) then begin
                            dec(move.next.x,1);
                        end else begin
                            inc(move.next.x,1);
                        end;
                    end;
                end else begin
                    if (abs(offset - ord(move.from.y) + ord('a'))=1) then begin
                        if(game.turn = White) then begin
                            inc(move.next.x,2);
                        end else begin
                            dec(move.next.x,2);
                        end;
                    end else if (abs(offset - ord(move.from.y) + ord('a'))=2) then begin
                        if(game.turn = White) then begin
                            inc(move.next.x,1);
                        end else begin
                            dec(move.next.x,1);
                        end;
                    end else begin
                        move.kind := None;
                        ReadAndProccessChineeseNotation := move;
                        exit;
                    end;
                end;
            end;
        end;
        {Уииии, наконец-то этот ужас закончился!}
        ReadAndProccessChineeseNotation := move;
    end;

    {считывание следующего хода в европейской нотации}
    function ReadNext(var game:Game_t):Move_t;
    var 
        c,w,dx,dy,offx,offy:char;
        m : Move_t;
        color:Color_t;
        from,next : Coordinate;
    begin
        color := game.turn;
        readln(c,dx,dy,w,offx,offy);
        m.kind := c;
        if(w <> '-') then begin
            m.kind := None;
        end;
        from.x := fixXCoordinates(ord(dx) - ord('0'),color);
        from.y := fixYCoordinates(dy,color);
        next.x := fixXCoordinates(ord(offx) - ord('0'),color);
        next.y := fixYCoordinates(offy,color);
        m.from := from;
        m.next := next;
        ReadNext := m;
    end;    {Стандартное расположение фигур на поле}
    function DefaultGame:Game_t;
    var
        i:integer;
        j:char;
        t:Game_t;
    begin
        new(t.OnMoveRead);
        t.hashes := nil;
        t.tail := nil;
        for i := 0 to Height - 1 do begin
            for j := 'a' to 'i' do begin 
                t.table[i,j].kind := None;
                t.table[i,j].color := White;
            end;
        end;
        t.turn := White;
        t.table[3,'a'].kind := Pawn;
        t.table[3,'a'].color := White;
        t.table[3,'c'] := t.table[3,'a'];
        t.table[3,'e'] := t.table[3,'c'];
        t.table[0,'a'].kind := Rock;
        t.table[0,'b'].kind := Horse;
        t.table[0,'c'].kind := Elephant;
        t.table[0,'d'].kind := Advisor;
        t.table[0,'e'].kind := General;
        t.table[2,'b'].kind := Canon;
        t.table[0,'a'].kind := Rock;
        for j := 'f' to 'i' do begin
            for i := 0 to 3 do begin
                t.table[i,j] := t.table[i,chr(ord('a') + 8 + ord('a') - ord(j))];
            end; 
        end;
        for j := 'a' to 'i' do begin
            for i := 6 to 9 do begin
                t.table[i,j].kind := t.table[9 - i,j].kind;
                t.table[i,j].color := Black;
            end; 
        end;
        DefaultGame := t;
    end;
    {DEBUG расположение фигур на поле}
    function DebugGame:Game_t;
    var
        i:integer;
        j:char;
        t:Game_t;
    begin
        new(t.OnMoveRead);
        t.hashes := nil;
        t.tail := nil;
        for i := 0 to Height - 1 do begin
            for j := 'a' to 'i' do begin 
                t.table[i,j].kind := None;
                t.table[i,j].color := White;
            end;
        end;
        t.turn := White;
        t.table[0,'e'].kind := General;
        t.table[9,'e'].kind := General;
        t.table[9,'e'].color := Black;
        t.table[8,'e'].color := Black;
        t.table[9,'d'].color := Black;
        t.table[8,'e'].kind := Advisor;
        t.table[9,'d'].kind := Advisor;
        t.table[0,'d'].kind := Advisor;
        t.table[0,'f'].kind := Advisor;
        t.table[0,'c'].kind := Elephant;
        t.table[0,'g'].kind := Elephant;
        t.table[2,'d'].kind := Rock;
        t.table[2,'d'].color := Black;
        t.table[2,'b'].kind := Pawn;
        t.table[2,'b'].color := Black;
        t.table[3,'f'].kind := Canon;
        t.table[3,'f'].color := Black;
        t.table[4,'e'].kind := Canon;
        t.table[4,'e'].color := Black;
        t.table[5,'g'].kind := Rock;
        t.table[6,'h'].kind := Horse;
        t.table[6,'e'].kind := Canon;
        t.table[8,'c'].kind := Canon;
        t.table[8,'g'].kind := Rock;
        t.table[7,'e'].color := Black;
        t.table[9,'h'].kind := Pawn;
        t.table[7,'e'].kind := Elephant;
        t.table[9,'i'].kind := Horse;
        DebugGame := t;
    end;
    {Процедура печати таблицы на экран с учетом различной разметки для каждого игрока}
    procedure PrintTable(var g:Game_t);
    var 
        i,fixedX:integer;
        j,fixedKind,fixedY:char;
        fig:Figure;
    begin
        writeln('  +--------------------+');
        for i := Height-1 downto 0 do begin
            fixedX := fixXCoordinates(i,g.turn);
            write(i,' | ');
            for j := 'a' to 'i' do begin
                fixedY := fixYCoordinates(j,g.turn);
                fig := g.table[fixedX,fixedY];
                fixedKind := fig.kind;
                if (fig.color = Black)  and (fig.kind <> None) then fixedKind := lowercase(fixedKind);
                if (fixedKind = None) then fixedKind := ' ';
                write(fixedKind,' ');
            end;
            writeln(' |');
        end; 
        writeln('  +--------------------+');
        write('    ');
        for j := 'a' to 'i' do 
            write(j,' ');
        writeln;
    end;
    {Функция для дебага}
    function ASSERT(var game:Game_t; b:boolean; s:string):integer;
    begin
        PrintTable(game);
        if not b then begin writeln(s); ASSERT := 1 div ord(b); end;
        ASSERT := 0;
    end; 
    {Функция взятия генерала того же цвета, что и текущий ход.}
    
    function GetGeneral(var g:Game_t; color:Color_t):Coordinate;
    var
        i,off:integer;
        j:char;
        c:Coordinate;
    begin
        off := ord(color)*7;
        for i := 0+off to 2+off do begin
            for j:= 'd' to 'f' do begin
                if (g.table[i,j].kind = General) then begin
                    c.x := i;
                    c.y := j;
                    GetGeneral := c;
                    exit;
                end;
            end;
        end;
        ASSERT(g,false,'Unreachable');
    end;
    function GetGeneral(var g:Game_t):Coordinate;
    begin
        GetGeneral := GetGeneral(g,g.turn);
    end;
    {Корректность координаты}
    function IsCorrectCoord(const c:Coordinate): boolean;
    begin
        IsCorrectCoord := (c.x in [0..9]) and (c.y in ['a'..'i']);
    end;
    {Свободность слота}
    function IsFreeSlot(const c:Coordinate; var t:Table_t):boolean;
    begin
        IsFreeSlot := t[c.x,c.y].kind = None;
    end;
    {проверка на занятость слота вражеской фигурой}
    function IsEnemySlot(const color:Color_t; const c:Coordinate;var t:Table_t):boolean;
    begin
        IsEnemySlot := (not IsFreeSlot(c,t)) and (t[c.x,c.y].color <> color);
    end;
    {Следующие функции вида IsCorrect*Move  - функции проверки корректности хода в завимости от фигуры, предполагается, что координаты корректны}
    function IsCorrectRockMove(const move:Move_t;var g:Game_t):boolean;
    var 
        i,dx,dy,nx,ex:integer;
        j,ny,ey:char;
        c:Coordinate;
    begin
        dx := move.next.x - move.from.x;
        dy := ord(move.next.y) - ord(move.from.y);
        if (dx*dy = 0) and (dx + dy <> 0) then begin
            if (dx = 0) then begin
                ex := move.next.x;
                nx := move.next.x;
                if (move.next.y > move.from.y) then begin
                    ny := succ(move.from.y);
                    ey := pred(move.next.y);
                end else begin
                    ey := pred(move.from.y);
                    ny := succ(move.next.y);
                end; 
            end else begin
                ey := move.next.y;
                ny := move.next.y;
                if (move.next.x > move.from.x) then begin
                    nx := succ(move.from.x);
                    ex := pred(move.next.x);
                end else begin
                    ex := pred(move.from.x);
                    nx := succ(move.next.x);
                end; 
            end;
            for i := nx to ex do begin
                for j := ny to ey do begin
                    c.x := i;
                    c.y := j;
                    if not IsFreeSlot(c,g.table) then begin
                        IsCorrectRockMove := false;
                        exit;
                    end; 
                end;
            end;
            IsCorrectRockMove := true;
        end else
            IsCorrectRockMove := false;
    end;
    
    function IsCorrectHorseMove(const move:Move_t;var g:Game_t):boolean;
    var
        dx,dy:integer;
        c:Coordinate;
    begin
        c := move.from;
        dx := move.next.x - move.from.x;
        dy := ord(move.next.y) - ord(move.from.y);
        if ([abs(dx),abs(dy)] <> [1,2]) then begin
            IsCorrectHorseMove := false;
            exit;
        end;
        if abs(dx) > abs(dy) then begin
            inc(c.x, 1-2*integer(dx < 0));
            if not IsFreeSlot(c,g.table) then begin
                IsCorrectHorseMove := false;
                exit;
            end;
        end else begin
            inc(c.y, 1-2*integer(dy < 0));
            if not IsFreeSlot(c,g.table) then begin
                IsCorrectHorseMove := false;
                exit;
            end;
        end;
        IsCorrectHorseMove := true;
    end;
    
    function IsCorrectElephantMove(const move:Move_t;var g:Game_t):boolean;
    var
        dx,dy:integer;
    begin
        dx := abs(move.next.x - move.from.x);
        dy := abs(ord(move.next.y) - ord(move.from.y));
        IsCorrectElephantMove := (((dx = dy) and (dx = 2) )) and (not ((g.turn = White) and (move.next.x in [5..9]) or (g.turn = Black) and (move.next.x in [0..4]))); 
    end;
    
    function IsCorrectAdvisorMove(const move:Move_t;var g:Game_t):boolean;
    var
        dx,dy:integer;
    begin
        dx := abs(move.next.x - move.from.x);
        dy := abs(ord(move.next.y) - ord(move.from.y));
        IsCorrectAdvisorMove := (dx*dy = 1) and (move.next.x in [0,1,2,7,8,9]) and (move.next.y in ['d','e','f']);

    end;
    
    function IsCorrectGeneralMove(const move:Move_t;var g:Game_t):boolean;
    var
        dx,dy:integer;
    begin
        if (g.table[move.next.x,move.next.y].kind = General) and (g.table[move.next.x,move.next.y].color<>g.turn) then begin
            IsCorrectGeneralMove := IsCorrectRockMove(move,g);
            exit;
        end;
        dx := abs(move.next.x - move.from.x);
        dy := abs(ord(move.next.y) - ord(move.from.y));
        IsCorrectGeneralMove := (dx + dy = 1) and (move.next.x in [0,1,2,7,8,9]) and (move.next.y in ['d','e','f']);
    end;
    
    function IsCorrectCanonMove(const move:Move_t;var g:Game_t):boolean;
    var 
        dx,dy,i,ex,nx:integer;
        j,ey,ny:char;
        foundFigure:boolean;
        c:Coordinate;
    begin
        if (IsFreeSlot(move.next,g.table)) then
            IsCorrectCanonMove := IsCorrectRockMove(move,g)
        else begin
            dx := move.next.x - move.from.x;
            dy := ord(move.next.y) - ord(move.from.y);
            if (dx*dy <> 0) then begin
                IsCorrectCanonMove := false;
                exit;
            end;
            if (dx = 0) then begin
                ex := move.next.x;
                nx := move.next.x;
                if (move.next.y > move.from.y) then begin
                    ny := succ(move.from.y);
                    ey := pred(move.next.y);
                end else begin
                    ey := pred(move.from.y);
                    ny := succ(move.next.y);
                end; 
            end else begin
                ey := move.next.y;
                ny := move.next.y;
                if (move.next.x > move.from.x) then begin
                    nx := succ(move.from.x);
                    ex := pred(move.next.x);
                end else begin
                    ex := pred(move.from.x);
                    nx := succ(move.next.x);
                end; 
            end;
            foundFigure := false;
            for i := nx to ex do begin
                for j := ny to ey do begin
                    c.x := i;
                    c.y := j;
                    if not IsFreeSlot(c,g.table) then begin
                        if foundFigure then begin
                            IsCorrectCanonMove := false;
                            exit;
                        end else
                            foundFigure := true;
                    end; 
                end;
            end;
            IsCorrectCanonMove := foundFigure;
        end;
    end;
    
    function IsCorrectPawnMove(const move:Move_t;var g:Game_t):boolean;
    var 
        dx,dy:integer;
        isDyPossible:boolean;
    begin
        dx := (1 - 2*(ord(g.turn)))*(move.next.x - move.from.x);
        if (dx < 0) then begin
            IsCorrectPawnMove := false;
            exit;
        end;
        dy := abs(ord(move.next.y) - ord(move.from.y));
        isDyPossible := (g.turn = White) and (move.from.x >=5) or (g.turn = Black) and (move.from.x <=4);
        if dy <> 0 then begin
            IsCorrectPawnMove := (dy = 1) and (isDyPossible) and (dx = 0);
            exit;
        end;
        IsCorrectPawnMove := dx = 1;
    end;
    {Общая проверка корректности хода для всех фигур.}
    function IsCorrectMove(const move:Move_t;var g:Game_t):boolean;
    begin
        if (not IsCorrectCoord(move.from)) or (not IsCorrectCoord(move.next)) or (g.table[move.from.x,move.from.y].kind <> move.kind) or IsEnemySlot(g.turn,move.from,g.table) or  
            (not IsFreeSlot(move.next,g.table)) and (not IsEnemySlot(g.turn,move.next,g.table)) then begin
            IsCorrectMove := false;
            exit;
        end;
        IsCorrectMove := false;
        case move.kind of 
            Pawn: IsCorrectMove := IsCorrectPawnMove(move,g);
            Elephant: IsCorrectMove := IsCorrectElephantMove(move,g);
            Rock: IsCorrectMove := IsCorrectRockMove(move,g);
            General: IsCorrectMove := IsCorrectGeneralMove(move,g);
            Advisor: IsCorrectMove := IsCorrectAdvisorMove(move,g);
            Horse: IsCorrectMove := IsCorrectHorseMove(move,g);
            Canon: IsCorrectMove := IsCorrectCanonMove(move,g);
            None : IsCorrectMove := false;
        end;
    end;
    {Проверка на шах.}
    function IsInCheck(var g:Game_t):boolean;
    var
        i:integer;
        c:Coordinate;
        list:FigureList;
        move:Move_t;
    begin
        list := GetEnemyFigures(g);
        c := GetGeneral(g);
        g.turn := Color_t(1 - ord(g.turn));
        move.next := c;
        IsInCheck := false;
        for i := 1 to 16 do begin
            move.kind := list[i].kind;
            move.from := list[i].position;
            if(IsCorrectMove(move,g)) then begin
                IsInCheck := true;
           //     writeln('Check from:', move.kind, ' ', move.from.x, move.from.y);
                break;
            end;
        end;
        g.turn := Color_t(1 - ord(g.turn));
    end;
    {Процедура добавление хода в список ходов.}
    procedure AddMove(var res:MovesList; var move:Move_t);
    begin
        inc(res.length);
        res.moves[res.length] := move;
    end;
    {Следующие функции генерируют всевозможные хода для каждой фигуры}
    procedure GenerateAllPawnAndGeneralMoves(var res:MovesList; var g:Game_t; fig:FigureInfo);
    var
        move:Move_t;
    begin
        move.from := fig.position;
        move.kind := fig.kind;
        move.next := move.from;
        inc(move.next.x);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        dec(move.next.x,2);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.y);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        dec(move.next.y,2);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
    end;    

    procedure GenerateAllHorseMoves(var res:MovesList; var g:Game_t; fig:FigureInfo);
    var
        move:Move_t;
    begin
        move.from := fig.position;
        move.kind := fig.kind;
        move.next := move.from;
        inc(move.next.x,1);
        inc(move.next.y,2);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.x,1);
        inc(move.next.y,-2);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.x,-1);
        inc(move.next.y,2);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.x,-1);
        inc(move.next.y,-2);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.x,2);
        inc(move.next.y,1);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.x,2);
        inc(move.next.y,-1);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.x,-2);
        inc(move.next.y,1);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.x,-2);
        inc(move.next.y,-1);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
    end;

    procedure GenerateAllElephantMoves(var res:MovesList; var g:Game_t; fig:FigureInfo);
    var
        move:Move_t;
    begin
        move.from := fig.position;
        move.kind := fig.kind;
        move.next := move.from;
        inc(move.next.x,2);
        inc(move.next.y,2);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.x,2);
        inc(move.next.y,-2);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.x,-2);
        inc(move.next.y,2);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.x,-2);
        inc(move.next.y,-2);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
    end;    
    procedure GenerateAllAdvisorMoves(var res:MovesList; var g:Game_t; fig:FigureInfo);
    var
        move:Move_t;
    begin
        move.from := fig.position;
        move.kind := fig.kind;
        move.next := move.from;
        inc(move.next.x,1);
        inc(move.next.y,1);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.x,1);
        inc(move.next.y,-1);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.x,-1);
        inc(move.next.y,1);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.x,-1);
        inc(move.next.y,-1);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
    end;    
    
    procedure GenerateAllRockAndCanonMoves(var res:MovesList; var g:Game_t; fig:FigureInfo);
    var
        move:Move_t;
        i:integer;
        j:char;
    begin
        move.from := fig.position;
        move.kind := fig.kind;
        move.next := move.from;
        for i := 1 to 10 do begin
            for j := 'a' to 'j' do begin
                move.next.x := i;
                move.next.y := j;
                if(IsCorrectMove(move,g)) then
                    AddMove(res,move);
            end;
        end;
    end;    
    {Общая процедура генерации ходов}
    procedure GenerateMovesForFigure(var g:Game_t;var res:MovesList;fig:FigureInfo);
    begin
        case fig.kind of 
            Pawn : GenerateAllPawnAndGeneralMoves( res, g, fig );
            Elephant : GenerateAllElephantMoves( res, g, fig );
            Rock : GenerateAllRockAndCanonMoves( res, g, fig );
            General : GenerateAllPawnAndGeneralMoves( res, g, fig );
            Advisor : GenerateAllAdvisorMoves( res, g, fig );
            Horse : GenerateAllHorseMoves( res, g, fig );
            Canon : GenerateAllRockAndCanonMoves( res, g, fig );
        end;

    end;    
    {Генерация всех ходов для всех фигур}
    function GenerateAllPossibleMoves(var g:Game_t):MovesList;
    var
        figures:FigureList;
        res:MovesList;
        i:integer;
    begin
        g.turn := Color_t(1 - ord(g.turn));
        figures := GetEnemyFigures(g);
        g.turn := Color_t(1 - ord(g.turn));
        res.length := 0;
        
        for i := 1 to 16 do begin
            GenerateMovesForFigure(g,res,figures[i]);
        end;    
        
        GenerateAllPossibleMoves := res;

    end;
    {Проверка на сохранение шаха после хода}
    function CheckPossible(move:Move_t; var g:Game_t):boolean;
    var 
        tmp1,tmp2:Figure;
    begin
        tmp1 := g.table[move.from.x,move.from.y];
        tmp2 := g.table[move.next.x,move.next.y];
        MakeMove(g,move);
        CheckPossible := IsInCheck(g);
      
      //  writeln('DEBUG: CheckPossible');
     //   PrintTable(g);
        g.table[move.from.x,move.from.y] := tmp1;
        g.table[move.next.x,move.next.y] := tmp2;
    end;
    {Проверка на мат: рассматриваем всевозможные ходы и шах после них}
    function IsInMate(var g:Game_t):boolean;
    var
        moves:MovesList;
        i:integer;
    begin
        moves := GenerateAllPossibleMoves(g);
        IsInMate := true;
   //     writeln('DEBUG: IsInMate');
        
        for i := 1 to moves.length do begin
            if not CheckPossible(moves.moves[i],g) then begin
                IsInMate := false;
                break;
            end; 
        end;
    end;
    function CalcTableValueForPlayer(var game:Game_t):longint;
    var
        i:integer;
        j:char;
        res:longint = 0;
        move:Move_t;
        fig:FigureInfo;
      {  function DegreeOfFreedom(coord:Coordinate):longint;
        var res:longint = 0;
        begin
            if(coord.x <> 9) then begin
                if(game.table[coord.x + 1,coord.y].kind = None) then
                    inc(res);
            end else
                inc(res);
            if(coord.x <> 0) then begin
                if(game.table[coord.x - 1,coord.y].kind = None) then
                    inc(res);
            end else
                inc(res);
            if(coord.y <> 'i') then begin
                if(game.table[coord.x,succ(coord.y)].kind = None) then
                    inc(res);
            end else
                inc(res);
            if(coord.y <> 'a') then begin
                if(game.table[coord.x,pred(coord.y)].kind = None) then
                    inc(res);
            end else
                inc(res);
            DegreeOfFreedom := res;
        end;}
    begin
        move.next := GetGeneral(game,Color_t(1-ord(game.turn)));
        move.kind := General;
        for i := 0 to Height - 1 do begin
            for j := 'a' to 'i' do begin
            fig.kind := game.table[i,j].kind;
            fig.position.x := i;
            fig.position.y := j;
                res := res + (integer(game.turn = game.table[i,j].color))*FigureCost(fig,game){ + DegreeOfFreedom(fig.position)};
            end;
            move.from := fig.position;
            if(IsCorrectMove(move,game)) then
                inc(res,FigureCost(fig,game) shr 1);
        end;
        CalcTableValueForPlayer := res;
    end;
    function CalcTableValueForOppositePlayer(var game:Game_t):longint;
    begin
        ChangeTurn(game);
        CalcTableValueForOppositePlayer := CalcTableValueForPlayer(game);
        ChangeTurn(game);
    end;
    
    procedure qSort(var game:Game_t;var ar: MovesList);
        function MakesCheck(move: Move_t):boolean;
        begin
            move.from := move.next;
            ChangeTurn(game);
            move.next := GetGeneral(game);
            ChangeTurn(game);
            MakesCheck := IsCorrectMove(move,game);
        end;
      // Вложенная функция сортировки для рекурсивного вызова
      // Нужна, чтобы не передавать в вызов основной функции границы массива
        procedure sort(var ar: MoveArray; low, high: integer);
        var i, j: integer;
            wsp: Move_t;
            m:integer;
        begin
        // repeat
            i:=low; j:=high; // Взятие среднего опорного элемента
          
            m := FigureCostMove(ar[(i+j) div 2],game);{
            if(MakesCheck(ar[(i+j) div 2])) then
                m := 10;}
            repeat
                while (FigureCostMove(ar[i],game)>m) {or (MakesCheck(ar[i])) and (10 > m)} do 
                    Inc(i); 
                while (FigureCostMove(ar[j],game)<m) {or (not MakesCheck(ar[j])) and (10 < m)} do 
                    Dec(j); 
                if i<=j then begin
                    wsp:=ar[i]; 
                    ar[i]:=ar[j]; 
                    ar[j]:=wsp;
                    Inc(i); 
                    Dec(j);
                end;
            until i>j;
        // if (j - low) < (high - i) then begin 
            if low<j then sort(ar, low, j);
        // low := i;
        //   end 
        // else begin
            if i<high then sort(ar, i, high);
        // high := j;
        // end; 
        //until low = high;
        end;
    begin
      sort(ar.moves,1,ar.length);
    end;
    
    function AlphaBetaPuring(var game:Game_t;depth, alpha,beta, ply:longint):longint;
    var
        moves:MovesList;
        tmp2,tmp1:Figure;
        i:integer;
        val:longint;
        flag:boolean = false;
    begin
       // writeln(ply,' ', depth,' ', alpha, ' ', beta);
        if(depth = 0) then begin
            AlphaBetaPuring := CalcTableValueForPlayer(game) - CalcTableValueForOppositePlayer(game);
            exit;
        end;
        moves := GenerateAllPossibleMoves(game);
        qSort(game,moves);
        for i := 1 to moves.length do begin
            tmp1 := game.table[moves.moves[i].from.x,moves.moves[i].from.y];
            tmp2 := game.table[moves.moves[i].next.x,moves.moves[i].next.y];
            //if(tmp2.kind = General) then begin
            //    AlphaBetaPuring := -MateValue;
            //    exit;
            //end;
           if( not CheckPossible(moves.moves[i],game)) then begin
                MakeMove(game,moves.moves[i]);
                ChangeTurn(game);
                val := -AlphaBetaPuring(game, depth -1,-beta,-alpha,ply+1);
                if(val > alpha) then begin
                    if (val >= beta) then begin
              //          writeln(alpha, ' ', beta, ' ', depth, ' ', ord(game.turn), ' ',val);
                        AlphaBetaPuring := beta;
                        flag := true;
                    end;
                    alpha := val;
                end;
                ChangeTurn(game);
                game.table[moves.moves[i].from.x,moves.moves[i].from.y] := tmp1;
                game.table[moves.moves[i].next.x,moves.moves[i].next.y] := tmp2;
                if flag then
                    break;
            end;
        end;
        if(moves.length  = 0) then begin
            if (IsInCheck(game)) then begin
                AlphaBetaPuring := -MateValue + ply
            end else begin
                AlphaBetaPuring := -PatValue;
            end;
        end else if not flag then 
            AlphaBetaPuring := alpha;
    end;
    function AIMove(var game:Game_t; depth:integer):boolean;
    var
        moves:MovesList; 
        i:integer;
        tmp1,tmp2:Figure;
        maxmove:Move_t;
        maxval,alphabeta:longint;
    begin
        AIMove := true;
        maxval :=  MateValue;
        moves := GenerateAllPossibleMoves(game);
        for i := 1 to moves.length do begin {Обработка первого уровня дерева, корневого, то есть, если мы хотим расчет на N полуходов, то в вызове функции ABP должна быть глубина N-1.}
            if(not CheckPossible(moves.moves[i],game)) then begin
                tmp1 := game.table[moves.moves[i].from.x,moves.moves[i].from.y];
                tmp2 := game.table[moves.moves[i].next.x,moves.moves[i].next.y];
                MakeMove(game,moves.moves[i]);
                ChangeTurn(game);
                alphabeta := AlphaBetaPuring(game,depth - 1,-maxval,MateValue,1);{Итого у нас расчет на 4 полухода.}
                if alphabeta <= maxval then begin
                    maxmove := moves.moves[i];
                    maxval := alphabeta;
                end;
                ChangeTurn(game);
                game.table[moves.moves[i].from.x,moves.moves[i].from.y] := tmp1;
                game.table[moves.moves[i].next.x,moves.moves[i].next.y] := tmp2;
            end;
        end;
        game.table[maxmove.next.x,maxmove.next.y] := game.table[maxmove.from.x,maxmove.from.y];
        game.table[maxmove.from.x,maxmove.from.y].kind := None;
        ChangeTurn(game);
    end;    
    {Считывание хода  и его исполнение в случае корректности}
    function PlayMove(var g:Game_t; depth:integer):boolean;
    var
        m:Move_t;
    begin
        PlayMove := true;
        write('Input >');
        m := g.OnMoveRead^(g);
        
        while (not IsCorrectMove(m,g)) or CheckPossible(m,g) do begin
            write('Incorrect! >');
            m := g.OnMoveRead^(g);
        end;
        
        if g.turn = Black then 
            g.turn := White 
        else 
            g.turn := Black;
        
        {тк ход пешки вперед необратим и убийство фигуры - то все позиции не могут уже повториться}
        if(g.table[m.next.x,m.next.y].kind <> None) or (m.kind = Pawn) and (m.from.x <> m.next.x) then begin
            ResetHashes(g);
        end;
        MakeMove(g,m);
    end;
    {Случайное расположение фигур, если сгенерировалась расстановка в матом - перегенерация.}
    function RandomGame(const _blackAmount,_whiteAmount:integer):Game_t;
    var
        coord,g1,g2:Coordinate;
        game:Game_t;
        j:char;
        move:Move_t;
        n,i,blackAmount,whiteAmount:integer;
        Counter: array ['A'..'Z',Color_t] of Integer;
        Limits: array ['A'..'Z'] of integer;
        Figures: array [1..7] of char = ('G','A','R','S','C','H','E');
        procedure Generate(color:Color_t);
        begin
            repeat 
                n := random(7) + 1;
                j := Figures[n];
            until not (Counter[j][color] >= Limits[j]);
            repeat
                if j = 'E' then begin
                    coord := RandomCoordinate(game,0+ord(color)*5,4+ord(color)*5,'a','i')
                end else if j = 'A' then begin
                    coord := RandomCoordinate(game,0+ord(color)*7,2+ord(color)*7,'d','f')
                end else begin
                    coord := RandomCoordinate(game,0,9,'a','i');
                end;
            until game.table[coord.x,coord.y].kind = None;
            inc(Counter[j][color]);
            game.table[coord.x,coord.y].kind := j;
            game.table[coord.x,coord.y].color := color;
        end;
    begin
        move.kind := General;
        blackAmount := _blackAmount;
        whiteAmount := _whiteAmount;
        new(game.OnMoveRead);
        game.hashes := nil;
        game.tail := nil;
        for i := 0 to Height - 1 do begin
            for j := 'a' to 'i' do begin 
                game.table[i,j].kind := None;
                game.table[i,j].color := White;
            end;
        end;
        for j := 'A' to 'Z' do begin
            Counter[j][White] := 0;
            Counter[j][Black] := 0;
            Limits[j] := 0;
        end;
        game.turn := White;
        coord := RandomCoordinate(game,0,2,'d','f');
        game.table[coord.x,coord.y].color := White;
        game.table[coord.x,coord.y].kind := General;
        g1 := coord;
        coord := RandomCoordinate(game,7,9,'d','f');
        game.table[coord.x,coord.y].color := Black;
        game.table[coord.x,coord.y].kind := General;
        g2 := coord;
        Limits['H'] := 2;
        Limits['E'] := 2;
        Limits['A'] := 2;
        Limits['S'] := 5;
        Limits['C'] := 2;
        Limits['R'] := 2; 
        dec(blackAmount);
        dec(whiteAmount);
        while( blackAmount + whiteAmount > 0) do begin
            if(blackAmount > 0) then begin
                Generate(Black);
                dec(blackAmount);
            end;
            if(whiteAmount > 0) then begin
                Generate(White);
                dec(whiteAmount);
            end;
        end;
        move.from := g1;
        move.next := g2;
        if(IsInMate(game)) or IsCorrectMove(move,game) then begin
            RandomGame := RandomGame(_blackAmount,_whiteAmount);
            dispose(game.OnMoveRead);
        end else begin
            game.turn := Black;
            move.next := g1;
            move.from := g2;
            if(IsInMate(game)) or IsCorrectMove(move,game) then begin
                RandomGame := RandomGame(_blackAmount,_whiteAmount);
                dispose(game.OnMoveRead);
            end else begin
                game.turn := White;
                RandomGame := game;
            end;
        end;
    end;
    {Главная процедура, точка входа игры, вечный цикл - цикл игры. Игра до тех пор, пока один их игроков не получит мат/вечный шах/4ех кратное повторение}
    procedure Play(game:Game_t);
    var 
        check:boolean;
        movesCount:integer = 0;
    begin
        check := IsInCheck(game);
        while true do begin
            inc(movesCount);
            PrintTable(game);

            if IsInMate(game) then begin 
                if check then begin
                    write('Mate!');
                    if(game.turn = White) then begin
                        writeln(' Black wins!') 
                    end else begin
                        writeln(' White wins!');
                    end;
                end else
                    writeln('Pat!');
                break;
            end;
            if(game.turn = White) then begin
                game.PlayerOne^(game,SearchDepth - ord(movesCount < HalfMovesDescrease))
            end else begin
                game.PlayerTwo^(game,SearchDepth - ord(movesCount < HalfMovesDescrease));
            end;
            
            check := IsInCheck(game);
            
            case (UpdateHash(game)) of
            4:  begin{Вау, ничья, аш 4 хода уже повторилось}
                    PrintTable(game);
                    writeln('Draw!');
                    break;
                end;
            1,2:begin end;
            3:  begin{2 повторения с шахом, дающий шах - проиграл, мвахахахаха}
                    PrintTable(game);
                    if check then begin
                        if(game.turn = White) then begin
                            writeln('Infinite check! White wins!')
                        end else begin 
                            writeln('Infinite check! Black wins!');
                        end;
                        break;
                    end;
                end;
            end;
        end;
    end;
    {Главная точка входа, меню выбора/интерфейс.}
    procedure Main;
    var
        P1,P2,v,game_type,notation:char; 
        blackAmount,whiteAmount:integer; 
        chinese:boolean;
        game:Game_t;
    begin
        writeln('Chinese Chess! Welcome!');
        writeln('Game types:');
        writeln(' N) Default game');
        writeln(' D) Debug game');
        writeln(' R) Random game');
        
        repeat
            write('Enter type:');
            readln(game_type);
        until (game_type in ['D','N','R']);
        
        if(game_type = 'R') then begin
            repeat
                write('Input range for random game(2 numbers in 1..16, black and white):');
                readln(blackAmount,whiteAmount);
            until ((blackAmount in [1..16]) and (whiteAmount in [1..16]));
        end;
        
        repeat 
            write('Chinese or euro notation?[C - for chinese/E - for euro]:');
            readln(notation);
        until (notation in ['C','E']);
        chinese := notation = 'C';
        
        repeat
            write('Input game type(PvP,EvE,PvE,EvP):');
            readln(P1,v,P2);
        until ((P1 in ['P','E']) and (P2 in ['P','E']) and (v = 'v'));
        
        if(game_type ='R') then begin
            game := RandomGame(blackAmount,whiteAmount);
        end else if(game_type = 'D') then begin
            game := DebugGame;
        end else
            game := DefaultGame;
        if(chinese) then
            game.OnMoveRead^ := @ReadAndProccessChineeseNotation{Люблю костыли}
        else
            game.OnMoveRead^ := @ReadNext;

        new(game.PlayerTwo);
        new(game.PlayerOne);

        if(P1 = 'P') then 
            game.PlayerOne^ := @PlayMove
        else
            game.PlayerOne^ := @AIMove;

        if(P2 = 'P') then 
            game.PlayerTwo^ := @PlayMove
        else
            game.PlayerTwo^ := @AIMove;
        UpdateHash(game);
        game.turn := White;
        Play(game);
        ResetHashes(game);
        
        dispose(game.OnMoveRead);
        dispose(game.PlayerTwo);
        dispose(game.PlayerOne);
    end;
begin
    randomize;
    {Запуск игры}
    Main; {Ненавижу китайскую нотацию.}
end.
