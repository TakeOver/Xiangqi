const 
    Height = 10;
    Width = 9;
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
    {Для проверки мата}
    MovesList = record 
        moves: array[1..200] of Move_t;
        length:integer;
    end;
    {Главная структура игры.}
    PMoveHandler = ^MoveHandler;
    Game_t = record
        table:Table_t;
        turn:Color_t;
        hashes,tail:PHashList;
        OnMoveRead : PMoveHandler;
    end;
    MoveHandler = function(var game:Game_t):Move_t;
    {Функция рассчета Хэша от таблицы.} {$I-}
    function HashTable(const g:Game_t):int64;
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
        HashTable := h;
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
    {Функция для дебага}
    function ASSERT(b:boolean; s:string):integer;
    begin
        if not b then begin writeln(s); ASSERT := 1 div ord(b); end;
        ASSERT := 0;
    end; 
    {Добавление элемента в конец списка фигур}
    procedure PushToList(var fList:FigureList; const f:Figure_t; const c:Coordinate; const x:integer);
    begin
        fList[x].kind := f;
        fList[x].position := c;
    end;
    {Функция взятия всех фигур, что еще живы.}
    function GetEnemyFigures(const g:Game_t):FigureList;
    var
        count,i:integer;
        j:char;
        list:FigureList;
        c:Coordinate;
    begin
        count := 0;
        for i := 0 to 9 do begin
            for j:= 'a' to 'i' do begin
                if (g.table[i,j].color <> g.turn) and (g.table[i,j].kind <> None) then begin
                    inc(count);
                    c.x := i; c.y := j;
                    PushToList(list,g.table[i,j].kind,c,count);
                end;
            end;
        end;
        GetEnemyFigures := list;
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
                write(offset,' ');
                if(game.turn = Black) then 
                    offset := Width  + offset
                else 
                    dec(offset);
                writeln(offset);
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
    procedure PrintTable(const g:Game_t);
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
    {Функция взятия генерала того же цвета, что и текущий ход.}
    function GetGeneral(const g:Game_t):Coordinate;
    var
        i,off:integer;
        j:char;
        c:Coordinate;
    begin
        off := ord(g.turn)*7;
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
        ASSERT(false,'Unreachable');
    end;
    {Корректность координаты}
    function IsCorrectCoord(const c:Coordinate): boolean;
    begin
        IsCorrectCoord := (c.x in [0..9]) and (c.y in ['a'..'i']);
    end;
    {Свободность слота}
    function IsFreeSlot(const c:Coordinate; const t:Table_t):boolean;
    begin
        IsFreeSlot := t[c.x,c.y].kind = None;
    end;
    {проверка на занятость слота вражеской фигурой}
    function IsEnemySlot(const color:Color_t; const c:Coordinate; const t:Table_t):boolean;
    begin
        IsEnemySlot := (not IsFreeSlot(c,t)) and (t[c.x,c.y].color <> color);
    end;
    {Следующие функции вида IsCorrect*Move  - функции проверки корректности хода в завимости от фигуры, предполагается, что координаты корректны}
    function IsCorrectRockMove(const move:Move_t;const g:Game_t):boolean;
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
    
    function IsCorrectHorseMove(const move:Move_t;const g:Game_t):boolean;
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
    
    function IsCorrectElephantMove(const move:Move_t;const g:Game_t):boolean;
    var
        dx,dy:integer;
    begin
        dx := abs(move.next.x - move.from.x);
        dy := abs(ord(move.next.y) - ord(move.from.y));
        IsCorrectElephantMove := (((dx = dy) and (dx = 2) )) and (not ((g.turn = White) and (move.next.x in [5..9]) or (g.turn = Black) and (move.next.x in [0..4]))); 
    end;
    
    function IsCorrectAdvisorMove(const move:Move_t;const g:Game_t):boolean;
    var
        dx,dy:integer;
    begin
        dx := abs(move.next.x - move.from.x);
        dy := abs(ord(move.next.y) - ord(move.from.y));
        IsCorrectAdvisorMove := (dx*dy = 1) and (move.next.x in [0,1,2,7,8,9]) and (move.next.y in ['d','e','f']);

    end;
    
    function IsCorrectGeneralMove(const move:Move_t;const g:Game_t):boolean;
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
    
    function IsCorrectCanonMove(const move:Move_t;const g:Game_t):boolean;
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
    
    function IsCorrectPawnMove(const move:Move_t;const g:Game_t):boolean;
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
            IsCorrectPawnMove := (dy = 1) and (isDyPossible);
            exit;
        end;
        IsCorrectPawnMove := dx = 1;
    end;
    {Общая проверка корректности хода для всех фигур.}
    function IsCorrectMove(const move:Move_t;const g:Game_t):boolean;
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
        move.next := move.from;
        dec(move.next.x);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        inc(move.next.y);
        if(IsCorrectMove(move,g)) then 
            AddMove(res,move);
        move.next := move.from;
        dec(move.next.y);
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
        g.table[move.from.x,move.from.y].kind := None;
        g.table[move.next.x,move.next.y] := tmp1;
        
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
    {Считывание хода  и его исполнение в случае корректности}
    procedure PlayMove(var g:Game_t);
    var
        m:Move_t;
    begin
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
        
        g.table[m.next.x,m.next.y] := g.table[m.from.x,m.from.y];
        g.table[m.from.x,m.from.y].kind := None;
    end;
    {Главная процедура, точка входа игры, вечный цикл - цикл игры. Игра до тех пор, пока один их игроков не получит мат/вечный шах/4ех кратное повторение}
    procedure Play;
    var 
        game : Game_t;
        check:boolean;
    begin
        game := DefaultGame;
        game.OnMoveRead^ := @ReadAndProccessChineeseNotation;{Люблю костыли}
        check := false;
        UpdateHash(game);
        while true do begin
            PrintTable(game);
            //writeln(HashTable(game));

            if check then begin 
                if IsInMate(game) then begin
                    write('Mate!');
                    if(game.turn = White) then begin
                        writeln(' Black wins!') 
                    end else begin
                        writeln(' White wins!');
                    end;
                    break;
                end;
            end;
            PlayMove(game);
            
            check := IsInCheck(game);
            
            case (UpdateHash(game)) of
            4:  begin{Вау, ничья, аш 4 хода уже повторилось}
                    writeln('Draw!');
                    break;
                end;
            1,3:begin end;
            2:  begin{2 повторения с шахом, дающий шах - проиграл, мвахахахаха}
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
        ResetHashes(game);
        dispose(game.OnMoveRead);
    end;

begin
    {Запуск игры}
    Play; {Ненавижу китайскую нотацию.}
end.
