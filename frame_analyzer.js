// 単位変換定数
const UNIT_CONVERSION = {
    // 断面性能の単位変換係数（cm → mm）
    CM4_TO_MM4: 1e4,    // 断面二次モーメント（cm⁴ → mm⁴）
    CM3_TO_MM3: 1e3,    // 断面係数（cm³ → mm³）
    CM2_TO_MM2: 1e2,    // 断面積（cm² → mm²）
    
    // 材料特性の基準値（N/mm²）
    E_STEEL: 2.05e5,    // 鋼材の弾性係数
    G_STEEL: 7.7e4,     // 鋼材のせん断弾性係数
};

// 断面性能の単位変換関数
function convertSectionProperties(props) {
    return {
        E: UNIT_CONVERSION.E_STEEL,  // N/mm²
        G: UNIT_CONVERSION.G_STEEL,  // N/mm²
        I: props.I * UNIT_CONVERSION.CM4_TO_MM4,  // cm⁴ → mm⁴
        A: props.A * UNIT_CONVERSION.CM2_TO_MM2,  // cm² → mm²
        Z: props.Z * UNIT_CONVERSION.CM3_TO_MM3   // cm³ → mm³
    };
}

document.addEventListener('DOMContentLoaded', () => {
    // DOM Elements
    const elements = {
        nodesTable: document.getElementById('nodes-table').getElementsByTagName('tbody')[0],
        membersTable: document.getElementById('members-table').getElementsByTagName('tbody')[0],
        nodeLoadsTable: document.getElementById('node-loads-table').getElementsByTagName('tbody')[0],
        memberLoadsTable: document.getElementById('member-loads-table').getElementsByTagName('tbody')[0],
        addNodeBtn: document.getElementById('add-node-btn'),
        addMemberBtn: document.getElementById('add-member-btn'),
        addNodeLoadBtn: document.getElementById('add-node-load-btn'),
        addMemberLoadBtn: document.getElementById('add-member-load-btn'),
        calculateBtn: document.getElementById('calculate-btn'),
        calculateAndAnimateBtn: document.getElementById('calculate-and-animate-btn'),
        presetSelector: document.getElementById('preset-selector'),
        displacementResults: document.getElementById('displacement-results'),
        reactionResults: document.getElementById('reaction-results'),
        forceResults: document.getElementById('force-results'),
        errorMessage: document.getElementById('error-message'),
        modelCanvas: document.getElementById('model-canvas'),
        displacementCanvas: document.getElementById('displacement-canvas'),
        momentCanvas: document.getElementById('moment-canvas'),
        axialCanvas: document.getElementById('axial-canvas'),
        shearCanvas: document.getElementById('shear-canvas'),
        modeSelectBtn: document.getElementById('mode-select'),
        modeAddNodeBtn: document.getElementById('mode-add-node'),
        modeAddMemberBtn: document.getElementById('mode-add-member'),
        undoBtn: document.getElementById('undo-btn'),
        nodeContextMenu: document.getElementById('node-context-menu'),
        memberPropsPopup: document.getElementById('member-props-popup'),
        nodeLoadPopup: document.getElementById('node-load-popup'),
        nodeCoordsPopup: document.getElementById('node-coords-popup'),
        addMemberPopup: document.getElementById('add-member-popup'),
        gridToggle: document.getElementById('grid-toggle'),
        gridSpacing: document.getElementById('grid-spacing'),
        animScaleInput: document.getElementById('anim-scale-input'),
        saveBtn: document.getElementById('save-btn'),
        loadBtn: document.getElementById('load-btn'),
        reportBtn: document.getElementById('report-btn'),
        ratioCanvas: document.getElementById('ratio-canvas'),
        sectionCheckResults: document.getElementById('section-check-results'),
        loadTermRadios: document.querySelectorAll('input[name="load-term"]'),
        resetModelBtn: document.getElementById('reset-model-btn'),
        autoScaleBtn: document.getElementById('auto-scale-btn'),
        zoomInBtn: document.getElementById('zoom-in-btn'),
        zoomOutBtn: document.getElementById('zoom-out-btn'),
    };

    let panZoomState = { scale: 1, offsetX: 0, offsetY: 0, isInitialized: false };
    let lastResults = null;
    let lastSectionCheckResults = null;
    let lastDisplacementScale = 0;

    const dispScaleInput = document.getElementById('disp-scale-input');
    dispScaleInput.addEventListener('change', (e) => {
        if(lastResults) {
            const newScale = parseFloat(e.target.value);
            if(!isNaN(newScale)) {
                drawDisplacementDiagram(lastResults.nodes, lastResults.members, lastResults.D, lastResults.memberLoads, newScale);
            }
        }
    });

    // Global State
    let canvasMode = 'select';
    let firstMemberNode = null;
    let selectedNodeIndex = null;
    let selectedMemberIndex = null;
    let isDragging = false;
    let isDraggingCanvas = false;
    let lastMouseX = 0;
    let lastMouseY = 0;
    let historyStack = [];
    const resolutionScale = 2.0;
    let newMemberDefaults = { E: '205000', F: '235', I: '18400', A: '2340', Z: '1230', i_conn: 'rigid', j_conn: 'rigid' };
    
    // --- Matrix Math Library ---
    const mat = { create: (rows, cols, value = 0) => Array(rows).fill().map(() => Array(cols).fill(value)), multiply: (A, B) => { const C = mat.create(A.length, B[0].length); for (let i = 0; i < A.length; i++) { for (let j = 0; j < B[0].length; j++) { for (let k = 0; k < A[0].length; k++) { C[i][j] += A[i][k] * B[k][j]; } } } return C; }, transpose: A => A[0].map((_, colIndex) => A.map(row => row[colIndex])), add: (A, B) => A.map((row, i) => row.map((val, j) => val + B[i][j])), subtract: (A, B) => A.map((row, i) => row.map((val, j) => val - B[i][j])), solve: (A, b) => { const n = A.length; const aug = A.map((row, i) => [...row, b[i][0]]); for (let i = 0; i < n; i++) { let maxRow = i; for (let k = i + 1; k < n; k++) { if (Math.abs(aug[k][i]) > Math.abs(aug[maxRow][i])) maxRow = k; } [aug[i], aug[maxRow]] = [aug[maxRow], aug[i]]; if (aug[i][i] === 0) continue; for (let k = i + 1; k < n; k++) { const factor = aug[k][i] / aug[i][i]; for (let j = i; j < n + 1; j++) aug[k][j] -= factor * aug[i][j]; } } const x = mat.create(n, 1); for (let i = n - 1; i >= 0; i--) { let sum = 0; for (let j = i + 1; j < n; j++) sum += aug[i][j] * x[j][0]; if (aug[i][i] === 0 && aug[i][n] - sum !== 0) return null; x[i][0] = aug[i][i] === 0 ? 0 : (aug[i][n] - sum) / aug[i][i]; } return x; } };
    
    // --- State and History Management ---
    const getCurrentState = () => {
        const state = { nodes: [], members: [], nodeLoads: [], memberLoads: [] };
        Array.from(elements.nodesTable.rows).forEach(row => {
            state.nodes.push({
                x: row.cells[1].querySelector('input').value,
                y: row.cells[2].querySelector('input').value,
                support: row.cells[3].querySelector('select').value
            });
        });
        Array.from(elements.membersTable.rows).forEach(row => {
            const e_select = row.cells[3].querySelector('select');
            const e_input = row.cells[3].querySelector('input[type="number"]');
            const strengthInputContainer = row.cells[4].firstElementChild;
            const strengthType = strengthInputContainer.dataset.strengthType;
            let strengthValue;
            if (strengthType === 'F-value' || strengthType === 'Fc' || strengthType === 'F-stainless' || strengthType === 'F-aluminum') {
                strengthValue = strengthInputContainer.querySelector('input').value;
            } else if (strengthType === 'wood-type') {
                strengthValue = strengthInputContainer.querySelector('select').value;
            }

            state.members.push({
                i: row.cells[1].querySelector('input').value,
                j: row.cells[2].querySelector('input').value,
                E: e_select.value === 'custom' ? e_input.value : e_select.value,
                strengthType: strengthType,
                strengthValue: strengthValue,
                I: row.cells[5].querySelector('input').value,
                A: row.cells[6].querySelector('input').value,
                Z: row.cells[7].querySelector('input').value,
                i_conn: row.cells[9].querySelector('select').value,
                j_conn: row.cells[10].querySelector('select').value,
                Zx: row.dataset.zx, Zy: row.dataset.zy, ix: row.dataset.ix, iy: row.dataset.iy
            });
        });
        Array.from(elements.nodeLoadsTable.rows).forEach(row => {
            state.nodeLoads.push({ node: row.cells[0].querySelector('input').value, px: row.cells[1].querySelector('input').value, py: row.cells[2].querySelector('input').value, mz: row.cells[3].querySelector('input').value });
        });
        Array.from(elements.memberLoadsTable.rows).forEach(row => {
            state.memberLoads.push({ member: row.cells[0].querySelector('input').value, w: row.cells[1].querySelector('input').value });
        });
        return state;
    };

    const pushState = () => { historyStack.push(getCurrentState()); };

    const restoreState = (state) => {
        if (!state) return;
        elements.nodesTable.innerHTML = '';
        elements.membersTable.innerHTML = '';
        elements.nodeLoadsTable.innerHTML = '';
        elements.memberLoadsTable.innerHTML = '';
        state.nodes.forEach(n => addRow(elements.nodesTable, [`#`, `<input type="number" value="${n.x}">`, `<input type="number" value="${n.y}">`, `<select><option value="free"${n.support==='free'?' selected':''}>自由</option><option value="pinned"${n.support==='pinned'?' selected':''}>ピン</option><option value="fixed"${n.support==='fixed'?' selected':''}>固定</option><option value="roller"${n.support==='roller'?' selected':''}>ローラー</option></select>`], false));
        state.members.forEach(m => {
            const I_m4 = parseFloat(m.I) * 1e-8;
            const A_m2 = parseFloat(m.A) * 1e-4;
            const Z_m3 = parseFloat(m.Z) * 1e-6;
            const newRow = addRow(elements.membersTable, [`#`, ...memberRowHTML(m.i, m.j, m.E, "235", I_m4, A_m2, Z_m3, m.i_conn, m.j_conn)], false);
            
            // Restore dynamic strength input
            const eSelect = newRow.cells[3].querySelector('select');
            const strengthCell = newRow.cells[4];
            eSelect.value = m.E === 'custom' ? 'custom' : m.E;
            eSelect.dispatchEvent(new Event('change')); // Trigger update
            const strengthInputContainer = strengthCell.firstElementChild;
            if (strengthInputContainer) {
                 if (m.strengthType === 'F-value' || m.strengthType === 'Fc' || m.strengthType === 'F-stainless' || m.strengthType === 'F-aluminum') {
                    strengthInputContainer.querySelector('input').value = m.strengthValue;
                    if(strengthInputContainer.querySelector('select')) strengthInputContainer.querySelector('select').value = 'custom';
                } else if (m.strengthType === 'wood-type') {
                    strengthInputContainer.querySelector('select').value = m.strengthValue;
                }
            }

            if(m.Zx) newRow.dataset.zx = m.Zx;
            if(m.Zy) newRow.dataset.zy = m.Zy;
            if(m.ix) newRow.dataset.ix = m.ix;
            if(m.iy) newRow.dataset.iy = m.iy;
        });
        state.nodeLoads.forEach(l => addRow(elements.nodeLoadsTable, [`<input type="number" value="${l.node}">`, `<input type="number" value="${l.px}">`, `<input type="number" value="${l.py}">`, `<input type="number" value="${l.mz}">`], false));
        state.memberLoads.forEach(l => addRow(elements.memberLoadsTable, [`<input type="number" value="${l.member}">`, `<input type="number" value="${l.w}">`], false));
        renumberTables();
        drawOnCanvas();
    };
    
    elements.undoBtn.onclick = () => { if (historyStack.length > 0) { const lastState = historyStack.pop(); if(lastState) restoreState(lastState); } };
    
    const addRow = (tableBody, cells, saveHistory = true) => {
        if(saveHistory) pushState();
        const newRow = tableBody.insertRow();
        cells.forEach(cellHTML => { const cell = newRow.insertCell(); cell.innerHTML = cellHTML; });
        const deleteCell = newRow.insertCell();
        deleteCell.innerHTML = '<button class="delete-row-btn">×</button>';
        
        if (tableBody === elements.membersTable) {
            newRow.cells[4].classList.add('section-check-item');
            newRow.cells[7].classList.add('section-check-item');
            const selectCell = newRow.insertCell();
            selectCell.innerHTML = `<button class="select-props-btn" title="鋼材データツールを開く">選択</button>`;
            newRow.insertBefore(selectCell, newRow.cells[8]); 

            const eSelect = newRow.cells[3].querySelector('select');
            const strengthCell = newRow.cells[4];
            eSelect.addEventListener('change', () => {
                const selectedOption = eSelect.options[eSelect.selectedIndex];
                let materialType = 'steel';
                if (selectedOption.textContent.includes('木材')) materialType = 'wood';
                else if (selectedOption.textContent.includes('コンクリート')) materialType = 'concrete';
                else if (selectedOption.textContent.includes('ステンレス')) materialType = 'stainless';
                else if (selectedOption.textContent.includes('アルミニウム')) materialType = 'aluminum';
                strengthCell.innerHTML = createStrengthInputHTML(materialType, `member-strength-${newRow.rowIndex}`);
            });
            eSelect.dispatchEvent(new Event('change'));

            deleteCell.querySelector('.delete-row-btn').onclick = () => {
                pushState();
                const deletedMemberNumber = newRow.rowIndex; 
                const loadsToDelete = Array.from(elements.memberLoadsTable.rows).filter(r => parseInt(r.cells[0].querySelector('input').value) - 1 === deletedMemberNumber);
                loadsToDelete.forEach(r => r.remove());
                Array.from(elements.memberLoadsTable.rows).forEach(r => { const input = r.cells[0].querySelector('input'); const current = parseInt(input.value); if(current - 1 > deletedMemberNumber) input.value = current - 1; });
                newRow.remove();
                renumberTables();
                drawOnCanvas();
            };
        } else if (tableBody === elements.nodesTable) {
            deleteCell.querySelector('.delete-row-btn').onclick = () => {
                pushState();
                const deletedNodeIndex = newRow.rowIndex - 1;
                const deletedNodeNumber = deletedNodeIndex + 1;
                const membersToDelete = [], membersToUpdate = [];
                Array.from(elements.membersTable.rows).forEach(r => {
                    const i = r.cells[1].querySelector('input'), j = r.cells[2].querySelector('input');
                    const c_i = parseInt(i.value), c_j = parseInt(j.value);
                    if (c_i === deletedNodeNumber || c_j === deletedNodeNumber) membersToDelete.push(r); 
                    else { if (c_i > deletedNodeNumber) membersToUpdate.push({ input: i, newValue: c_i - 1 }); if (c_j > deletedNodeNumber) membersToUpdate.push({ input: j, newValue: c_j - 1 }); }
                });
                const nodeLoadsToDelete = [], nodeLoadsToUpdate = [];
                Array.from(elements.nodeLoadsTable.rows).forEach(r => {
                    const n = r.cells[0].querySelector('input'); const current = parseInt(n.value);
                    if (current === deletedNodeNumber) nodeLoadsToDelete.push(r);
                    else if (current > deletedNodeNumber) nodeLoadsToUpdate.push({ input: n, newValue: current - 1 });
                });
                membersToDelete.forEach(r => r.remove());
                nodeLoadsToDelete.forEach(r => r.remove());
                membersToUpdate.forEach(item => item.input.value = item.newValue);
                nodeLoadsToUpdate.forEach(item => item.input.value = item.newValue);
                newRow.remove();
                renumberTables();
                drawOnCanvas();
            };
        } else {
            deleteCell.querySelector('.delete-row-btn').onclick = () => { pushState(); newRow.remove(); renumberTables(); drawOnCanvas(); };
        }
        newRow.querySelectorAll('input, select').forEach(el => { el.addEventListener('focus', pushState); el.addEventListener('change', () => drawOnCanvas()); });
        if (saveHistory) { renumberTables(); drawOnCanvas(); }
        return newRow;
    };

    const renumberTables = () => {
        elements.nodesTable.querySelectorAll('tr').forEach((row, i) => row.cells[0].textContent = i + 1);
        elements.membersTable.querySelectorAll('tr').forEach((row, i) => row.cells[0].textContent = i + 1);
    };
    
    const calculate = () => {
        try {
            elements.errorMessage.style.display = 'none';
            clearResults(); 
            const { nodes, members, nodeLoads, memberLoads } = parseInputs();
            const dof = nodes.length * 3;
            let K_global = mat.create(dof, dof);
            let F_global = mat.create(dof, 1);
            const fixedEndForces = {};
            memberLoads.forEach(load => {
                const member = members[load.memberIndex];
                const L = member.length, w = load.w;
                let fel;
                if (member.i_conn === 'rigid' && member.j_conn === 'rigid') { fel = [0, w*L/2, w*L**2/12, 0, w*L/2, -w*L**2/12]; } 
                else if (member.i_conn === 'pinned' && member.j_conn === 'rigid') { fel = [0, 3*w*L/8, 0, 0, 5*w*L/8, -w*L**2/8]; } 
                else if (member.i_conn === 'rigid' && member.j_conn === 'pinned') { fel = [0, 5*w*L/8, w*L**2/8, 0, 3*w*L/8, 0]; } 
                else { fel = [0, w*L/2, 0, 0, w*L/2, 0]; }
                const T_t = mat.transpose(member.T), feg = mat.multiply(T_t, fel.map(v => [v])), i = member.i, j = member.j;
                F_global[i*3][0] -= feg[0][0]; F_global[i*3+1][0] -= feg[1][0]; F_global[i*3+2][0] -= feg[2][0];
                F_global[j*3][0] -= feg[3][0]; F_global[j*3+1][0] -= feg[4][0]; F_global[j*3+2][0] -= feg[5][0];
                fixedEndForces[load.memberIndex] = fel;
            });
            nodeLoads.forEach(load => { const i = load.nodeIndex * 3; F_global[i][0] += load.px; F_global[i+1][0] += load.py; F_global[i+2][0] += load.mz; });
            members.forEach((member) => {
                const {k_local, T, i, j} = member;
                const T_t = mat.transpose(T), k_global_member = mat.multiply(mat.multiply(T_t, k_local), T);
                const indices = [i*3, i*3+1, i*3+2, j*3, j*3+1, j*3+2];
                for (let row = 0; row < 6; row++) for (let col = 0; col < 6; col++) K_global[indices[row]][indices[col]] += k_global_member[row][col];
            });
            const constraints = [];
            nodes.forEach((node, i) => {
                if (node.support === 'fixed') constraints.push(i*3, i*3+1, i*3+2);
                if (node.support === 'pinned') constraints.push(i*3, i*3+1);
                if (node.support === 'roller') constraints.push(i*3+1);
            });
            const reduced_indices = [...Array(dof).keys()].filter(i => !constraints.includes(i));
            if (reduced_indices.length === 0) {
                const D_global = mat.create(dof, 1), R = mat.multiply(F_global, [[-1]]);
                const memberForces = members.map((member, idx) => { const fel = fixedEndForces[idx] || [0,0,0,0,0,0]; return { N_i: fel[0], Q_i: fel[1], M_i: fel[2], N_j: fel[3], Q_j: fel[4], M_j: fel[5] }; });
                displayResults(D_global, R, memberForces, nodes, members, nodeLoads, memberLoads);
                return;
            }
            const K_reduced = mat.create(reduced_indices.length, reduced_indices.length), F_reduced = mat.create(reduced_indices.length, 1);
            reduced_indices.forEach((r_idx, i) => { F_reduced[i][0] = F_global[r_idx][0]; reduced_indices.forEach((c_idx, j) => { K_reduced[i][j] = K_global[r_idx][c_idx]; }); });
            const D_reduced = mat.solve(K_reduced, F_reduced);
            if (!D_reduced) throw new Error("解を求めることができませんでした。構造が不安定であるか、拘束が不適切である可能性があります。");
            const D_global = mat.create(dof, 1);
            reduced_indices.forEach((val, i) => { D_global[val][0] = D_reduced[i][0]; });
            const R = mat.subtract(mat.multiply(K_global, D_global), F_global);
            const memberForces = members.map((member, idx) => {
                const { T, k_local, i, j } = member;
                const d_global_member = [ ...D_global.slice(i * 3, i * 3 + 3), ...D_global.slice(j * 3, j * 3 + 3) ];
                const d_local = mat.multiply(T, d_global_member);
                let f_local = mat.multiply(k_local, d_local);
                if(fixedEndForces[idx]) { const fel_mat = fixedEndForces[idx].map(v=>[v]); f_local = mat.add(f_local, fel_mat); }
                return { N_i: f_local[0][0], Q_i: f_local[1][0], M_i: f_local[2][0], N_j: f_local[3][0], Q_j: f_local[4][0], M_j: f_local[5][0] };
            });
            displayResults(D_global, R, memberForces, nodes, members, nodeLoads, memberLoads);
        } catch (error) {
            elements.errorMessage.textContent = `エラー: ${error.message}`;
            elements.errorMessage.style.display = 'block';
            console.error(error);
        }
    };
    
    const parseInputs = () => {
        const nodes = Array.from(elements.nodesTable.rows).map((row, i) => ({ id: i + 1, x: parseFloat(row.cells[1].querySelector('input').value), y: parseFloat(row.cells[2].querySelector('input').value), support: row.cells[3].querySelector('select').value }));
        const members = Array.from(elements.membersTable.rows).map((row, index) => {
            const i = parseInt(row.cells[1].querySelector('input').value) - 1, j = parseInt(row.cells[2].querySelector('input').value) - 1;
            const e_select = row.cells[3].querySelector('select'), e_input = row.cells[3].querySelector('input[type="number"]');
            let E = (e_select.value === 'custom' ? parseFloat(e_input.value) : parseFloat(e_select.value)) * 1000;
            const strengthInputContainer = row.cells[4].firstElementChild;
            const strengthType = strengthInputContainer.dataset.strengthType;
            let strengthProps = { type: strengthType };
            if (strengthType === 'F-value' || strengthType === 'Fc' || strengthType === 'F-stainless' || strengthType === 'F-aluminum') {
                strengthProps.value = parseFloat(strengthInputContainer.querySelector('input').value);
            } else if (strengthType === 'wood-type') {
                strengthProps.value = strengthInputContainer.querySelector('select').value;
            }
            const I = parseFloat(row.cells[5].querySelector('input').value) * 1e-8;
            const A = parseFloat(row.cells[6].querySelector('input').value) * 1e-4;
            const Z = parseFloat(row.cells[7].querySelector('input').value) * 1e-6;
            const i_conn = row.cells[9].querySelector('select').value, j_conn = row.cells[10].querySelector('select').value;
            const Zx = parseFloat(row.dataset.zx) * 1e-6, Zy = parseFloat(row.dataset.zy) * 1e-6;
            const ix = parseFloat(row.dataset.ix) * 1e-2 || Math.sqrt(I / A), iy = parseFloat(row.dataset.iy) * 1e-2 || ix;
            if (isNaN(E) || !strengthProps.value || isNaN(I) || isNaN(A) || isNaN(Z)) throw new Error(`部材 ${index + 1} の物性値が無効です。`);
            if (i < 0 || j < 0 || i >= nodes.length || j >= nodes.length) throw new Error(`部材 ${index + 1} の節点番号が不正です。`);
            const ni = nodes[i], nj = nodes[j], dx = nj.x - ni.x, dy = nj.y - ni.y, L = Math.sqrt(dx**2 + dy**2);
            if(L === 0) throw new Error(`部材 ${index+1} の長さが0です。`);
            const c = dx/L, s = dy/L, T = [ [c,s,0,0,0,0], [-s,c,0,0,0,0], [0,0,1,0,0,0], [0,0,0,c,s,0], [0,0,0,-s,c,0], [0,0,0,0,0,1] ];
            const EAL=E*A/L, EIL=E*I/L, EIL2=E*I/L**2, EIL3=E*I/L**3;
            let k_local;
            if (i_conn === 'rigid' && j_conn === 'rigid') k_local = [[EAL,0,0,-EAL,0,0],[0,12*EIL3,6*EIL2,0,-12*EIL3,6*EIL2],[0,6*EIL2,4*EIL,0,-6*EIL2,2*EIL],[-EAL,0,0,EAL,0,0],[0,-12*EIL3,-6*EIL2,0,12*EIL3,-6*EIL2],[0,6*EIL2,2*EIL,0,-6*EIL2,4*EIL]];
            else if (i_conn === 'pinned' && j_conn === 'rigid') k_local = [[EAL,0,0,-EAL,0,0],[0,3*EIL3,0,0,-3*EIL3,3*EIL2],[0,0,0,0,0,0],[-EAL,0,0,EAL,0,0],[0,-3*EIL3,0,0,3*EIL3,-3*EIL2],[0,3*EIL2,0,0,-3*EIL2,3*EIL]];
            else if (i_conn === 'rigid' && j_conn === 'pinned') k_local = [[EAL,0,0,-EAL,0,0],[0,3*EIL3,3*EIL2,0,-3*EIL3,0],[0,3*EIL2,3*EIL,0,-3*EIL2,0],[-EAL,0,0,EAL,0,0],[0,-3*EIL3,-3*EIL2,0,3*EIL3,0],[0,0,0,0,0,0]];
            else k_local = [[EAL,0,0,-EAL,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[-EAL,0,0,EAL,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0]];
            return { i,j,E,strengthProps,I,A,Z,Zx,Zy,ix,iy,length:L,c,s,T,i_conn,j_conn,k_local };
        });
        const nodeLoads = Array.from(elements.nodeLoadsTable.rows).map((r, i) => { const n = parseInt(r.cells[0].querySelector('input').value) - 1; if (n < 0 || n >= nodes.length) throw new Error(`節点荷重 ${i+1} の節点番号が不正です。`); return { nodeIndex:n, px:parseFloat(r.cells[1].querySelector('input').value)||0, py:parseFloat(r.cells[2].querySelector('input').value)||0, mz:parseFloat(r.cells[3].querySelector('input').value)||0 }; });
        const memberLoads = Array.from(elements.memberLoadsTable.rows).map((r, i) => { const m = parseInt(r.cells[0].querySelector('input').value) - 1; if (m < 0 || m >= members.length) throw new Error(`部材荷重 ${i+1} の部材番号が不正です。`); return { memberIndex:m, w:parseFloat(r.cells[1].querySelector('input').value)||0 }; });
        return { nodes, members, nodeLoads, memberLoads };
    };
    
    const clearResults = () => {
        const canvases = [elements.displacementCanvas, elements.momentCanvas, elements.axialCanvas, elements.shearCanvas, elements.ratioCanvas];
        canvases.forEach(c => { if (c) { const ctx = c.getContext('2d'); ctx.clearRect(0, 0, c.width, c.height); } });
        const tables = [elements.displacementResults, elements.reactionResults, elements.forceResults, elements.sectionCheckResults];
        tables.forEach(t => { if(t) t.innerHTML = ''; });
        lastResults = null;
        lastSectionCheckResults = null;
    };
    
    const displayResults = (D, R, forces, nodes, members, nodeLoads, memberLoads) => {
        lastResults = { D, R, forces, nodes, members, nodeLoads, memberLoads };
        elements.errorMessage.style.display = 'none';
        let dispHTML = `<thead><tr><th>節点 #</th><th>変位 δx (mm)</th><th>変位 δy (mm)</th><th>回転角 θz (rad)</th></tr></thead><tbody>`; for (let i = 0; i < D.length / 3; i++) { dispHTML += `<tr><td>${i+1}</td><td>${(D[i*3][0]*1000).toFixed(2)}</td><td>${(D[i*3+1][0]*1000).toFixed(2)}</td><td>${D[i*3+2][0].toFixed(2)}</td></tr>`; } elements.displacementResults.innerHTML = dispHTML + '</tbody>';
        let reactHTML = `<thead><tr><th>節点 #</th><th>反力 Rx (kN)</th><th>反力 Ry (kN)</th><th>反力 Mz (kN・m)</th></tr></thead><tbody>`; nodes.forEach((n, i) => { if (n.support !== 'free') { const rx = -R[i*3][0]||0, ry = -R[i*3+1][0]||0, mz = -R[i*3+2][0]||0; reactHTML += `<tr><td>${i+1}</td><td>${rx.toFixed(2)}</td><td>${ry.toFixed(2)}</td><td>${mz.toFixed(2)}</td></tr>`; } }); elements.reactionResults.innerHTML = reactHTML + '</tbody>';
        let forceHTML = `<thead><tr><th>部材 #</th><th>始端 #i</th><th>終端 #j</th><th>軸力 N (kN)</th><th>せん断力 Q (kN)</th><th>曲げM (kN・m)</th></tr></thead><tbody>`; forces.forEach((f, i) => { const ni = members[i].i+1, nj = members[i].j+1; forceHTML += `<tr><td rowspan="2">${i+1}</td><td>${ni} (i端)</td><td>-</td><td>${(-f.N_i).toFixed(2)}</td><td>${f.Q_i.toFixed(2)}</td><td>${f.M_i.toFixed(2)}</td></tr><tr><td>-</td><td>${nj} (j端)</td><td>${f.N_j.toFixed(2)}</td><td>${(-f.Q_j).toFixed(2)}</td><td>${f.M_j.toFixed(2)}</td></tr>`; }); elements.forceResults.innerHTML = forceHTML + '</tbody>';
        drawDisplacementDiagram(nodes, members, D, memberLoads);
        drawMomentDiagram(nodes, members, forces, memberLoads);
        drawAxialForceDiagram(nodes, members, forces);
        drawShearForceDiagram(nodes, members, forces, memberLoads);
    };

// --- Canvas Drawing ---
    let lastDrawingContext = null;
    const getDrawingContext = (canvas) => {
        let nodes;
        try { nodes = parseInputs().nodes; } catch (e) { nodes = []; }
        if (!canvas) return null;
        
        const minX = nodes.length > 0 ? Math.min(...nodes.map(n => n.x)) : 0;
        const maxX = nodes.length > 0 ? Math.max(...nodes.map(n => n.x)) : 0;
        const minY = nodes.length > 0 ? Math.min(...nodes.map(n => n.y)) : 0;
        const maxY = nodes.length > 0 ? Math.max(...nodes.map(n => n.y)) : 0;
        const modelWidth = maxX - minX;
        const modelHeight = maxY - minY;
        
        const padding = 70;
        const containerRect = canvas.parentElement.getBoundingClientRect();
        
        // 検定比図の場合は、より大きな表示領域を確保
        const isRatioCanvas = canvas.id === 'ratio-canvas';
        const minHeight = isRatioCanvas ? 350 : 250;
        const maxHeight = isRatioCanvas ? 1200 : 800;
        
        // First, calculate the required scale and height
        let scale, offsetX, offsetY, requiredHeight;

        if (nodes.length === 0) {
            scale = 50; // An arbitrary scale for an empty grid
            requiredHeight = isRatioCanvas ? 500 : 400;
        } else if (modelWidth === 0 && modelHeight === 0) {
            // Single node or all nodes at the same location. Center the view on the first node.
            scale = 50; // Default zoom level
            requiredHeight = isRatioCanvas ? 500 : 400;
        } else {
            const scaleX = (containerRect.width - 2 * padding) / (modelWidth || 1);
            const scaleY = (containerRect.height - 2 * padding) / (modelHeight || 1);
            scale = Math.min(scaleX, scaleY) * 0.9;
            requiredHeight = modelHeight * scale + 2 * padding;

            // 検定比図の場合は、高さを調整
            if (isRatioCanvas) {
                requiredHeight = modelHeight * scale + 2 * padding;
            }

            requiredHeight = Math.max(minHeight, Math.min(maxHeight, requiredHeight));
        }

        canvas.style.height = `${requiredHeight}px`;

        const rect = canvas.getBoundingClientRect();
        const dpr = window.devicePixelRatio || 1;
        canvas.width = rect.width * dpr * resolutionScale;
        canvas.height = rect.height * dpr * resolutionScale;

        const ctx = canvas.getContext('2d');
        ctx.scale(dpr * resolutionScale, dpr * resolutionScale);
        ctx.clearRect(0, 0, canvas.width, canvas.height);
        ctx.font = "12px Arial";

        if (nodes.length === 0) {
            const offsetX = padding;
            const offsetY = rect.height - padding;
            const transform = (x, y) => ({ x: x * scale + offsetX, y: -y * scale + offsetY });
            return { ctx, transform, scale, offsetX, offsetY };
        }

        if (modelWidth === 0 && modelHeight === 0) {
            // Single node or all nodes at the same location. Center the view on the first node.
            const nodeX = nodes[0].x;
            const nodeY = nodes[0].y;
            offsetX = (rect.width / 2) - (nodeX * scale);
            offsetY = (rect.height / 2) + (nodeY * scale);
            const transform = (x, y) => ({ x: x * scale + offsetX, y: -y * scale + offsetY });
            return { ctx, transform, scale, offsetX, offsetY };
        }

        const isModelCanvas = canvas.id === 'model-canvas';

        if (isModelCanvas && panZoomState.isInitialized) {
            // モデル図が初期化済みの場合、既存のパン・ズーム情報を維持
            ({ scale, offsetX, offsetY } = panZoomState);
        } else {
            // 結果の図、またはモデル図の初回描画時は、常に中央に配置
            offsetX = padding + (rect.width - 2 * padding - modelWidth * scale) / 2 - minX * scale;
            offsetY = padding + (rect.height - 2 * padding - modelHeight * scale) / 2 + maxY * scale;

            if (isModelCanvas) {
                // モデル図の初回描画時のみ、状態を保存
                panZoomState = { scale, offsetX, offsetY, isInitialized: true };
            }
        }
        
        const transform = (x, y) => ({ x: x * scale + offsetX, y: -y * scale + offsetY });
        
        return { ctx, transform, scale, offsetX, offsetY };
    };
    const drawStructure = (ctx, transform, nodes, members, color, showNodeNumbers = true) => { ctx.strokeStyle = color; ctx.lineWidth = 2; members.forEach(m => { const start = transform(nodes[m.i].x, nodes[m.i].y); const end = transform(nodes[m.j].x, nodes[m.j].y); ctx.beginPath(); ctx.moveTo(start.x, start.y); ctx.lineTo(end.x, end.y); ctx.stroke(); }); nodes.forEach((n, i) => { const pos = transform(n.x, n.y); ctx.fillStyle = "#000"; ctx.beginPath(); ctx.arc(pos.x, pos.y, 4, 0, 2 * Math.PI); ctx.fill(); if (showNodeNumbers) { ctx.fillStyle = "#333"; ctx.fillText(i + 1, pos.x + 8, pos.y - 8); } }); };
    const drawConnections = (ctx, transform, nodes, members) => { ctx.fillStyle = 'white'; ctx.strokeStyle = '#333'; ctx.lineWidth = 1.5; const offset = 6; members.forEach(m => { const n_i = nodes[m.i]; const p_i = transform(n_i.x, n_i.y); if (m.i_conn === 'pinned') { const p_i_offset = { x: p_i.x + offset * m.c, y: p_i.y - offset * m.s }; ctx.beginPath(); ctx.arc(p_i_offset.x, p_i_offset.y, 3, 0, 2 * Math.PI); ctx.fill(); ctx.stroke(); } if (m.j_conn === 'pinned') { const n_j = nodes[m.j]; const p_j = transform(n_j.x, n_j.y); const p_j_offset = { x: p_j.x - offset * m.c, y: p_j.y + offset * m.s }; ctx.beginPath(); ctx.arc(p_j_offset.x, p_j_offset.y, 3, 0, 2 * Math.PI); ctx.fill(); ctx.stroke(); } }); };
    const drawBoundaryConditions = (ctx, transform, nodes) => { const size = 10; nodes.forEach(node => { if (node.support === 'free') return; const pos = transform(node.x, node.y); ctx.strokeStyle = '#008000'; ctx.fillStyle = '#008000'; ctx.lineWidth = 1.5; ctx.beginPath(); if (node.support === 'fixed') { ctx.moveTo(pos.x - size, pos.y + size); ctx.lineTo(pos.x + size, pos.y + size); for(let i=0; i < 5; i++){ ctx.moveTo(pos.x - size + i*size/2, pos.y + size); ctx.lineTo(pos.x - size + i*size/2 - size/2, pos.y + size + size/2); } } else if (node.support === 'pinned') { ctx.moveTo(pos.x, pos.y); ctx.lineTo(pos.x - size, pos.y + size); ctx.lineTo(pos.x + size, pos.y + size); ctx.closePath(); ctx.stroke(); ctx.moveTo(pos.x - size*1.2, pos.y + size); ctx.lineTo(pos.x + size*1.2, pos.y + size); } else if (node.support === 'roller') { ctx.moveTo(pos.x, pos.y); ctx.lineTo(pos.x - size, pos.y + size); ctx.lineTo(pos.x + size, pos.y + size); ctx.closePath(); ctx.stroke(); ctx.moveTo(pos.x - size, pos.y + size + 3); ctx.lineTo(pos.x + size, pos.y + size + 3); } ctx.stroke(); }); };
    const drawDimensions = (ctx, transform, nodes, members, labelManager, obstacles) => { const offset = 15; ctx.strokeStyle = '#0000ff'; ctx.lineWidth = 1; members.forEach(m => { const n1 = nodes[m.i]; const n2 = nodes[m.j]; const p1 = transform(n1.x, n1.y); const p2 = transform(n2.x, n2.y); const midX = (p1.x + p2.x) / 2; const midY = (p1.y + p2.y) / 2; const angle = Math.atan2(p2.y - p1.y, p2.x - p1.x); const offsetX = offset * Math.sin(angle); const offsetY = -offset * Math.cos(angle); const labelTargetX = midX + offsetX; const labelTargetY = midY + offsetY; const labelText = `${m.length.toFixed(2)}m`; ctx.fillStyle = '#0000ff'; labelManager.draw(ctx, labelText, labelTargetX, labelTargetY, obstacles); }); };
    const drawExternalLoads = (ctx, transform, nodes, members, nodeLoads, memberLoads, labelManager, obstacles) => { const arrowSize = 10; const loadScale = 3; ctx.strokeStyle = '#ff4500'; ctx.fillStyle = '#ff4500'; ctx.lineWidth = 1.5; nodeLoads.forEach(load => { if (load.px === 0 && load.py === 0 && load.mz === 0) return; const node = nodes[load.nodeIndex]; const pos = transform(node.x, node.y); if(load.px !== 0){ const dir = Math.sign(load.px); ctx.beginPath(); ctx.moveTo(pos.x - arrowSize * loadScale * dir, pos.y); ctx.lineTo(pos.x, pos.y); ctx.lineTo(pos.x - arrowSize * dir, pos.y - arrowSize/2); ctx.moveTo(pos.x, pos.y); ctx.lineTo(pos.x - arrowSize * dir, pos.y + arrowSize/2); ctx.stroke(); ctx.textAlign = dir > 0 ? 'right' : 'left'; ctx.textBaseline = 'middle'; ctx.fillText(`${load.px}kN`, pos.x - (arrowSize * loadScale + 5) * dir, pos.y); } if(load.py !== 0){ const dir = Math.sign(load.py); ctx.beginPath(); ctx.moveTo(pos.x, pos.y + arrowSize * loadScale * dir); ctx.lineTo(pos.x, pos.y); ctx.lineTo(pos.x - arrowSize/2, pos.y + arrowSize * dir); ctx.moveTo(pos.x, pos.y); ctx.lineTo(pos.x + arrowSize/2, pos.y + arrowSize * dir); ctx.stroke(); ctx.textAlign = 'center'; ctx.textBaseline = dir > 0 ? 'top' : 'bottom'; ctx.fillText(`${load.py}kN`, pos.x, pos.y + (arrowSize * loadScale + 5) * dir); } if(load.mz !== 0){ const dir = -Math.sign(load.mz); const r = arrowSize * 1.5; const arrowHeadSize = 5; const startAngle = Math.PI; const endAngle = Math.PI * 2.5; ctx.beginPath(); ctx.arc(pos.x, pos.y, r, startAngle, endAngle, dir < 0); ctx.stroke(); const endX = pos.x + r * Math.cos(endAngle); const endY = pos.y + r * Math.sin(endAngle); const smallAngleOffset = 0.05 * (dir > 0 ? -1 : 1); const beforeX = pos.x + r * Math.cos(endAngle + smallAngleOffset); const beforeY = pos.y + r * Math.sin(endAngle + smallAngleOffset); const tangentAngle = Math.atan2(endY - beforeY, endX - beforeX); ctx.beginPath(); ctx.moveTo(endX, endY); ctx.lineTo(endX - arrowHeadSize * Math.cos(tangentAngle - Math.PI / 6), endY - arrowHeadSize * Math.sin(tangentAngle - Math.PI / 6)); ctx.lineTo(endX - arrowHeadSize * Math.cos(tangentAngle + Math.PI / 6), endY - arrowHeadSize * Math.sin(tangentAngle + Math.PI / 6)); ctx.closePath(); ctx.fill(); ctx.textAlign = 'center'; ctx.textBaseline = 'bottom'; ctx.fillText(`${load.mz}kN·m`, pos.x, pos.y - r - 5); } }); memberLoads.forEach(load => { if (load.w === 0) return; const member = members[load.memberIndex]; const p1 = transform(nodes[member.i].x, nodes[member.i].y); const p2 = transform(nodes[member.j].x, nodes[member.j].y); const angle = Math.atan2(p2.y - p1.y, p2.x - p1.x); const numArrows = 5; const arrowLength = arrowSize * 1.5; const arrowHeadSize = 5; const dir = Math.sign(load.w); const perpVecX = Math.sin(angle); const perpVecY = -Math.cos(angle); const firstArrowTipX = p1.x + dir * arrowLength * perpVecX; const firstArrowTipY = p1.y + dir * arrowLength * perpVecY; const lastArrowTipX = p2.x + dir * arrowLength * perpVecX; const lastArrowTipY = p2.y + dir * arrowLength * perpVecY; ctx.beginPath(); ctx.moveTo(firstArrowTipX, firstArrowTipY); ctx.lineTo(lastArrowTipX, lastArrowTipY); ctx.stroke(); for (let i = 0; i <= numArrows; i++) { const ratio = i / numArrows; const memberX = p1.x + (p2.x - p1.x) * ratio; const memberY = p1.y + (p2.y - p1.y) * ratio; const baseX = memberX + dir * arrowLength * perpVecX; const baseY = memberY + dir * arrowLength * perpVecY; ctx.beginPath(); ctx.moveTo(baseX, baseY); ctx.lineTo(memberX, memberY); const headAngle = Math.atan2(memberY - baseY, memberX - baseX); ctx.moveTo(memberX, memberY); ctx.lineTo(memberX - arrowHeadSize * Math.cos(headAngle - Math.PI / 6), memberY - arrowHeadSize * Math.sin(headAngle - Math.PI / 6)); ctx.moveTo(memberX, memberY); ctx.lineTo(memberX - arrowHeadSize * Math.cos(headAngle + Math.PI / 6), memberY - arrowHeadSize * Math.sin(headAngle + Math.PI / 6)); ctx.stroke(); } const textOffset = arrowLength + 10; const textX = (p1.x + p2.x) / 2 + dir * textOffset * perpVecX; const textY = (p1.y + p2.y) / 2 + dir * textOffset * perpVecY; ctx.fillStyle = '#ff4500'; labelManager.draw(ctx, `${Math.abs(load.w)}kN/m`, textX, textY, obstacles); }); };
    const drawGrid = (ctx, transform, width, height) => { const { x: minX, y: maxY } = inverseTransform(0,0); const { x: maxX, y: minY } = inverseTransform(width, height); const spacing = parseFloat(elements.gridSpacing.value); if (isNaN(spacing) || spacing <= 0) return; ctx.strokeStyle = '#e9e9e9'; ctx.lineWidth = 1; const startX = Math.floor(minX / spacing) * spacing; for (let x = startX; x <= maxX; x += spacing) { const p1 = transform(x, minY); const p2 = transform(x, maxY); ctx.beginPath(); ctx.moveTo(p1.x, p1.y); ctx.lineTo(p2.x, p2.y); ctx.stroke(); } const startY = Math.floor(minY / spacing) * spacing; for (let y = startY; y <= maxY; y += spacing) { const p1 = transform(minX, y); const p2 = transform(maxX, y); ctx.beginPath(); ctx.moveTo(p1.x, p1.y); ctx.lineTo(p2.x, p2.y); ctx.stroke(); } };
    const LabelManager = () => { const drawnLabelBounds = []; const isOverlapping = (rect1, rect2) => !(rect1.x2 < rect2.x1 || rect1.x1 > rect2.x2 || rect1.y2 < rect2.y1 || rect1.y1 > rect2.y2); return { draw: (ctx, text, targetX, targetY, obstacles = [], bounds = null) => { const metrics = ctx.measureText(text); const w = metrics.width; const h = metrics.fontBoundingBoxAscent ?? 12; const padding = 6; const candidates = [ [w/2 + padding, -padding, 'left', 'bottom'], [-w/2 - padding, -padding, 'right', 'bottom'], [w/2 + padding, h + padding, 'left', 'top'], [-w/2 - padding, h + padding, 'right', 'top'], [0, -h - padding, 'center', 'bottom'], [0, h + padding, 'center', 'top'], [w/2 + padding, h/2, 'left', 'middle'], [-w/2 - padding, h/2, 'right', 'middle'] ]; for (const cand of candidates) { const x = targetX + cand[0]; const y = targetY + cand[1]; let rect; if (cand[2] === 'left') rect = { x1: x, y1: y - h, x2: x + w, y2: y }; else if (cand[2] === 'right') rect = { x1: x - w, y1: y - h, x2: x, y2: y }; else rect = { x1: x - w/2, y1: y - h, x2: x + w/2, y2: y }; const paddedRect = {x1: rect.x1 - padding, y1: rect.y1 - padding, x2: rect.x2 + padding, y2: rect.y2 + padding}; let isInvalid = false; for (const existingRect of [...drawnLabelBounds, ...obstacles]) { if (isOverlapping(paddedRect, existingRect)) { isInvalid = true; break; } } if (isInvalid) continue; if (bounds) { if (paddedRect.x1 < bounds.x1 || paddedRect.x2 > bounds.x2 || paddedRect.y1 < bounds.y1 || paddedRect.y2 > bounds.y2) { isInvalid = true; } } if (isInvalid) continue; ctx.textAlign = cand[2]; ctx.textBaseline = cand[3]; ctx.fillText(text, x, y); drawnLabelBounds.push(paddedRect); return; } }, clear: () => { drawnLabelBounds.length = 0; } }; };
    const drawOnCanvas = () => {
        const drawingCtx = getDrawingContext(elements.modelCanvas);
        if (!drawingCtx) return; // Should not happen with the modified getDrawingContext

        lastDrawingContext = drawingCtx;
        const { ctx, transform } = drawingCtx;
        try {
            if (elements.gridToggle.checked) {
                drawGrid(ctx, transform, elements.modelCanvas.clientWidth, elements.modelCanvas.clientHeight);
            }
            const { nodes, members, nodeLoads, memberLoads } = parseInputs();
            if (nodes.length > 0) {
                const labelManager = LabelManager();
                const nodeObstacles = nodes.map(n => {
                    const pos = transform(n.x, n.y);
                    const metrics = ctx.measureText(nodes.indexOf(n) + 1);
                    const textWidth = metrics.width;
                    return { x1: pos.x - 8, y1: pos.y - 8 - 12, x2: pos.x + 8 + textWidth, y2: pos.y + 8 };
                });
                drawStructure(ctx, transform, nodes, members, '#333', true);
                drawConnections(ctx, transform, nodes, members);
                drawBoundaryConditions(ctx, transform, nodes);
                drawDimensions(ctx, transform, nodes, members, labelManager, nodeObstacles);
                drawExternalLoads(ctx, transform, nodes, members, nodeLoads, memberLoads, labelManager, nodeObstacles);
                if (canvasMode === 'addMember' && firstMemberNode !== null) {
                    const node = nodes[firstMemberNode];
                    const pos = transform(node.x, node.y);
                    ctx.fillStyle = 'rgba(255, 165, 0, 0.5)';
                    ctx.beginPath();
                    ctx.arc(pos.x, pos.y, 8, 0, 2 * Math.PI);
                    ctx.fill();
                }
            }
        } catch (e) {
            console.error("Drawing error:", e);
        }
    };
    const drawDisplacementDiagram = (nodes, members, D_global, memberLoads, manualScale = null) => {
        const drawingCtx = getDrawingContext(elements.displacementCanvas);
        if (!drawingCtx) return;
        const { ctx, transform, scale } = drawingCtx;
        
        let dispScale = 0;
        if (D_global.length > 0) {
            if (manualScale !== null) {
                dispScale = manualScale;
            } else {
                let max_dx = 0, max_dy = 0;
                members.forEach((m, idx) => {
                    const L = m.length, c = m.c, s = m.s;
                    const d_global_member_vec = [ ...D_global.slice(m.i * 3, m.i * 3 + 3), ...D_global.slice(m.j * 3, m.j * 3 + 3) ];
                    const d_local_vec = mat.multiply(m.T, d_global_member_vec);
                    const [ui, vi, thi, uj, vj, thj] = d_local_vec.map(v => v[0]);
                    const load = memberLoads.find(l => l.memberIndex === idx), w = load ? load.w : 0, E = m.E, I = m.I;
                    for (let k = 0; k <= 20; k++) {
                        const x = (k / 20) * L, xi = x / L;
                        const N1 = 1 - 3*xi**2 + 2*xi**3, N2 = x * (1 - xi)**2, N3 = 3*xi**2 - 2*xi**3, N4 = (x**2 / L) * (xi - 1);
                        const u_local = (1 - xi) * ui + xi * uj, v_homogeneous = N1*vi + N2*thi + N3*vj + N4*thj;
                        let v_particular = 0;
                        if (w !== 0 && E > 0 && I > 0) {
                            if (m.i_conn === 'rigid' && m.j_conn === 'rigid') v_particular = (w * x**2 * (L - x)**2) / (24 * E * I);
                            else if (m.i_conn === 'pinned' && m.j_conn === 'pinned') v_particular = (w * x * (L**3 - 2 * L * x**2 + x**3)) / (24 * E * I);
                            else if (m.i_conn === 'rigid' && m.j_conn === 'pinned') v_particular = (w * x**2 * (3 * L**2 - 5 * L * x + 2 * x**2)) / (48 * E * I);
                            else if (m.i_conn === 'pinned' && m.j_conn === 'rigid') v_particular = (w * x * (L**3 - 3 * L * x**2 + 2 * x**3)) / (48 * E * I);
                        }
                        const v_local = v_homogeneous - v_particular;
                        max_dx = Math.max(max_dx, Math.abs(u_local * c - v_local * s));
                        max_dy = Math.max(max_dy, Math.abs(u_local * s + v_local * c));
                    }
                });
                // モデルの最大変位量 (モデル単位)
                const max_model_disp = Math.max(max_dx, max_dy);

                // 目標とする画面上の最大変位ピクセル数 (この値を変えると、変位図の見た目の大きさが変わります)
                const TARGET_MAX_DISP_PIXELS = 40;

                if (max_model_disp > 1e-12 && scale > 1e-12) {
                    // 表示倍率 = (目標ピクセル数) / (モデル単位の最大変位量 * 描画スケール)
                    const autoScale = TARGET_MAX_DISP_PIXELS / (max_model_disp * scale);
                    // 極端に大きい値や小さい値にならないように調整
                    dispScale = isFinite(autoScale) ? Math.max(0.1, Math.min(autoScale, 5000)) : 0;
                } else {
                    dispScale = 0;
                }
                lastDisplacementScale = dispScale;
                dispScaleInput.value = dispScale.toFixed(2);
            }
        }
        drawStructure(ctx, transform, nodes, members, '#ccc', true);
        ctx.fillStyle = '#333'; ctx.textAlign = 'left'; ctx.fillText(`表示倍率: ${dispScale.toFixed(2)} 倍`, 10, 20);
        ctx.strokeStyle = 'red'; ctx.lineWidth = 2;
        const maxIntermediateLabels = [];
        members.forEach((m, idx) => {
            const L = m.length, c = m.c, s = m.s, ni = nodes[m.i];
            const d_global_member_vec = [ ...D_global.slice(m.i * 3, m.i * 3 + 3), ...D_global.slice(m.j * 3, m.j * 3 + 3) ];
            const d_local_vec = mat.multiply(m.T, d_global_member_vec), [ui, vi, thi, uj, vj, thj] = d_local_vec.map(v => v[0]);
            const load = memberLoads.find(l => l.memberIndex === idx), w = load ? load.w : 0, E = m.E, I = m.I;
            let maxDispMag = 0, maxDispPoint = null;
            ctx.beginPath();
            for (let k = 0; k <= 20; k++) {
                const x = (k / 20) * L, xi = x / L;
                const N1=1-3*xi**2+2*xi**3, N2=x*(1-xi)**2, N3=3*xi**2-2*xi**3, N4=(x**2/L)*(xi-1);
                const u_local = (1-xi)*ui+xi*uj, v_homogeneous = N1*vi+N2*thi+N3*vj+N4*thj;
                let v_particular = 0;
                if (w !== 0 && E > 0 && I > 0) {
                    if (m.i_conn==='rigid'&&m.j_conn==='rigid') v_particular=(w*x**2*(L-x)**2)/(24*E*I);
                    else if(m.i_conn==='pinned'&&m.j_conn==='pinned')v_particular=(w*x*(L**3-2*L*x**2+x**3))/(24*E*I);
                    else if(m.i_conn==='rigid'&&m.j_conn==='pinned')v_particular=(w*x**2*(3*L**2-5*L*x+2*x**2))/(48*E*I);
                    else if(m.i_conn==='pinned'&&m.j_conn==='rigid')v_particular=(w*x*(L**3-3*L*x**2+2*x**3))/(48*E*I);
                }
                const v_local = v_homogeneous - v_particular;
                const disp_x_global=u_local*c-v_local*s, disp_y_global=u_local*s+v_local*c, dispMag=Math.sqrt(disp_x_global**2+disp_y_global**2);
                if (dispMag > maxDispMag) { maxDispMag=dispMag; const original_x=ni.x+x*c, original_y=ni.y+x*s; maxDispPoint={x:original_x,y:original_y,dx:disp_x_global,dy:disp_y_global,mag:maxDispMag}; }
                const p = transform(ni.x+x*c+disp_x_global*dispScale, ni.y+x*s+disp_y_global*dispScale);
                if (k === 0) ctx.moveTo(p.x, p.y); else ctx.lineTo(p.x, p.y);
            }
            ctx.stroke();
            const disp_i_mag = Math.sqrt(D_global[m.i*3][0]**2 + D_global[m.i*3+1][0]**2);
            const disp_j_mag = Math.sqrt(D_global[m.j*3][0]**2 + D_global[m.j*3+1][0]**2);
            if (maxDispPoint && maxDispMag > disp_i_mag && maxDispMag > disp_j_mag) { maxIntermediateLabels.push({x:maxDispPoint.x+maxDispPoint.dx*dispScale,y:maxDispPoint.y+maxDispPoint.dy*dispScale,label:`${(maxDispPoint.mag*1000).toFixed(2)}mm`}); }
        });
        const labelManager = LabelManager(), allObstacles = [];
        const rect = elements.displacementCanvas.getBoundingClientRect(), canvasBounds = { x1: 5, y1: 25, x2: rect.width - 5, y2: rect.height - 5 };
        nodes.forEach((n,i) => { const dx=D_global[i*3][0], dy=D_global[i*3+1][0]; const p_def = transform(n.x+dx*dispScale, n.y+dy*dispScale); allObstacles.push({x1:p_def.x-8,y1:p_def.y-8,x2:p_def.x+8,y2:p_def.y+8}); const p_orig = transform(n.x,n.y); const metrics = ctx.measureText(`${i+1}`); allObstacles.push({x1:p_orig.x+8,y1:p_orig.y-8-12,x2:p_orig.x+8+metrics.width,y2:p_orig.y-8}); });
        ctx.fillStyle='#00008b'; ctx.font="11px Arial";
        nodes.forEach((n, i) => { const dx_mm=D_global[i*3][0]*1000, dy_mm=D_global[i*3+1][0]*1000; if (Math.sqrt(dx_mm**2+dy_mm**2)>1e-3) { const dx=D_global[i*3][0], dy=D_global[i*3+1][0]; const p_def=transform(n.x+dx*dispScale,n.y+dy*dispScale); const labelText=`(${dx_mm.toFixed(2)}, ${dy_mm.toFixed(2)})mm`; labelManager.draw(ctx,labelText,p_def.x,p_def.y,allObstacles,canvasBounds); } });
        ctx.fillStyle='#8b0000';
        maxIntermediateLabels.forEach(lbl => { const p_def=transform(lbl.x,lbl.y); allObstacles.push({x1:p_def.x-8,y1:p_def.y-8,x2:p_def.x+8,y2:p_def.y+8}); labelManager.draw(ctx,lbl.label,p_def.x,p_def.y,allObstacles,canvasBounds); });
    };
    const drawMomentDiagram = (nodes, members, forces, memberLoads) => { const drawingCtx = getDrawingContext(elements.momentCanvas); if (!drawingCtx) return; const { ctx, transform, scale } = drawingCtx; const labelManager = LabelManager(); drawStructure(ctx, transform, nodes, members, '#ccc', false); const nodeObstacles = nodes.map(n => { const pos = transform(n.x, n.y); return {x1: pos.x - 12, y1: pos.y - 12, x2: pos.x + 12, y2: pos.y + 12}; }); let maxMoment = 0; forces.forEach((f, idx) => { const member = members[idx]; const load = memberLoads.find(l => l.memberIndex === idx); const w = load ? load.w : 0; const L = member.length; let localMax = Math.max(Math.abs(f.M_i), Math.abs(f.M_j)); if (w !== 0 && Math.abs(f.Q_i) > 1e-9) { const x_q_zero = f.Q_i / w; if (x_q_zero > 0 && x_q_zero < L) { const M_max_parabolic = -f.M_i * (1 - x_q_zero / L) + f.M_j * (x_q_zero / L) + w * L * x_q_zero / 2 - w * x_q_zero**2 / 2; localMax = Math.max(localMax, Math.abs(M_max_parabolic)); } } maxMoment = Math.max(maxMoment, localMax); }); const maxOffsetPixels = 60; let momentScale = 0; if (scale > 0 && maxMoment > 1e-9) { const maxOffsetModelUnits = maxOffsetPixels / scale; momentScale = maxOffsetModelUnits / maxMoment; } members.forEach((m, idx) => { const force = forces[idx]; const load = memberLoads.find(l => l.memberIndex === idx); const w = load ? load.w : 0; const n_i = nodes[m.i], n_j = nodes[m.j]; ctx.beginPath(); const start = transform(n_i.x, n_i.y); ctx.moveTo(start.x, start.y); const numPoints = 20; for (let i = 0; i <= numPoints; i++) { const x_local = (i / numPoints) * m.length, M_linear = -force.M_i * (1 - x_local / m.length) + force.M_j * (x_local / m.length), M_parabolic = w * m.length * x_local / 2 - w * x_local**2 / 2; const m_local = M_linear + M_parabolic, offset = -m_local * momentScale; const globalX = n_i.x + x_local * m.c - offset * m.s, globalY = n_i.y + x_local * m.s + offset * m.c; const pt = transform(globalX, globalY); ctx.lineTo(pt.x, pt.y); } const end = transform(n_j.x, n_j.y); ctx.lineTo(end.x, end.y); ctx.fillStyle = 'rgba(255, 0, 0, 0.2)'; ctx.strokeStyle = 'red'; ctx.lineWidth = 1; ctx.closePath(); ctx.fill(); ctx.stroke(); ctx.fillStyle = '#333'; if (Math.abs(force.M_i) > 1e-3) labelManager.draw(ctx, `${force.M_i.toFixed(2)}`, start.x, start.y, nodeObstacles); if (Math.abs(force.M_j) > 1e-3) labelManager.draw(ctx, `${force.M_j.toFixed(2)}`, end.x, end.y, nodeObstacles); if (w !== 0 && Math.abs(force.Q_i) > 1e-9) { const x_max = force.Q_i / w; if (x_max > 1e-6 && x_max < m.length - 1e-6) { const M_linear = -force.M_i*(1-x_max/m.length)+force.M_j*(x_max/m.length), M_parabolic=w*m.length*x_max/2-w*x_max**2/2; const M_max=M_linear+M_parabolic, offset=-M_max*momentScale; const globalX=n_i.x+x_max*m.c-offset*m.s, globalY=n_i.y+x_max*m.s+offset*m.c; const pt=transform(globalX,globalY); labelManager.draw(ctx,`${M_max.toFixed(2)}`,pt.x,pt.y,nodeObstacles); } } }); };
    const drawAxialForceDiagram = (nodes, members, forces) => { const drawingCtx = getDrawingContext(elements.axialCanvas); if (!drawingCtx) return; const { ctx, transform, scale } = drawingCtx; const labelManager = LabelManager(); drawStructure(ctx, transform, nodes, members, '#ccc', false); const nodeObstacles = nodes.map(n => { const pos = transform(n.x, n.y); return {x1: pos.x - 12, y1: pos.y - 12, x2: pos.x + 12, y2: pos.y + 12}; }); let maxAxial = 0; forces.forEach(f => maxAxial = Math.max(maxAxial, Math.abs(f.N_i), Math.abs(f.N_j))); const maxOffsetPixels = 40; let axialScale = 0; if (scale > 0 && maxAxial > 0) { const maxOffsetModelUnits = maxOffsetPixels / scale; axialScale = maxOffsetModelUnits / maxAxial; } members.forEach((m, idx) => { const N = -forces[idx].N_i, offset = -N * axialScale; const n_i = nodes[m.i], n_j = nodes[m.j]; const p1_offset_x = -offset*m.s, p1_offset_y = offset*m.c; const p1 = transform(n_i.x+p1_offset_x, n_i.y+p1_offset_y), p2=transform(n_j.x+p1_offset_x, n_j.y+p1_offset_y); const p_start=transform(n_i.x,n_i.y), p_end=transform(n_j.x,n_j.y); ctx.beginPath(); ctx.moveTo(p_start.x, p_start.y); ctx.lineTo(p1.x, p1.y); ctx.lineTo(p2.x, p2.y); ctx.lineTo(p_end.x, p_end.y); ctx.closePath(); ctx.fillStyle = N > 0 ? 'rgba(255,0,0,0.2)' : 'rgba(0,0,255,0.2)'; ctx.strokeStyle = N > 0 ? 'red' : 'blue'; ctx.fill(); ctx.stroke(); ctx.fillStyle = '#333'; if (Math.abs(N) > 1e-3) { const mid_offset_x=p1_offset_x*0.5, mid_offset_y=p1_offset_y*0.5; const mid_pos=transform((n_i.x+n_j.x)/2+mid_offset_x, (n_i.y+n_j.y)/2+mid_offset_y); labelManager.draw(ctx,`${N.toFixed(2)}`,mid_pos.x,mid_pos.y,nodeObstacles); } }); };
    const drawShearForceDiagram = (nodes, members, forces, memberLoads) => { const drawingCtx = getDrawingContext(elements.shearCanvas); if (!drawingCtx) return; const { ctx, transform, scale } = drawingCtx; const labelManager = LabelManager(); drawStructure(ctx, transform, nodes, members, '#ccc', false); const nodeObstacles = nodes.map(n => { const pos = transform(n.x, n.y); return {x1: pos.x - 12, y1: pos.y - 12, x2: pos.x + 12, y2: pos.y + 12}; }); let maxShear = 0; forces.forEach(f => maxShear = Math.max(maxShear, Math.abs(f.Q_i), Math.abs(f.Q_j))); const maxOffsetPixels = 50; let shearScale = 0; if (scale > 0 && maxShear > 0) { const maxOffsetModelUnits = maxOffsetPixels / scale; shearScale = maxOffsetModelUnits / maxShear; } members.forEach((m, idx) => { const Q_i = forces[idx].Q_i, Q_j = -forces[idx].Q_j; const load=memberLoads.find(l=>l.memberIndex===idx), w=load?load.w:0; const n_i=nodes[m.i], n_j=nodes[m.j]; const offset_i=-Q_i*shearScale; const p1_offset_x=-offset_i*m.s, p1_offset_y=offset_i*m.c; const p1=transform(n_i.x+p1_offset_x, n_i.y+p1_offset_y); const p_start=transform(n_i.x,n_i.y), p_end=transform(n_j.x,n_j.y); ctx.beginPath(); ctx.moveTo(p_start.x, p_start.y); ctx.lineTo(p1.x, p1.y); let p2; if (w === 0) { const offset_j=-Q_j*shearScale; const p2_offset_x=-offset_j*m.s, p2_offset_y=offset_j*m.c; p2=transform(n_j.x+p2_offset_x, n_j.y+p2_offset_y); ctx.lineTo(p2.x, p2.y); } else { const numPoints = 10; for(let i=1; i<=numPoints; i++){ const x_local=(i/numPoints)*m.length, Q_local=Q_i-w*x_local, offset_local=-Q_local*shearScale; const globalX=n_i.x+x_local*m.c-offset_local*m.s, globalY=n_i.y+x_local*m.s+offset_local*m.c; p2=transform(globalX, globalY); ctx.lineTo(p2.x, p2.y); } } ctx.lineTo(p_end.x, p_end.y); ctx.closePath(); ctx.fillStyle = Q_i > 0 ? 'rgba(0,128,0,0.2)' : 'rgba(255,165,0,0.2)'; ctx.strokeStyle = Q_i > 0 ? 'green' : 'orange'; ctx.fill(); ctx.stroke(); ctx.fillStyle = '#333'; if(Math.abs(Q_i)>1e-3) labelManager.draw(ctx,`${Q_i.toFixed(2)}`,p1.x,p1.y,nodeObstacles); if(Math.abs(Q_j)>1e-3) labelManager.draw(ctx,`${Q_j.toFixed(2)}`,p2.x,p2.y,nodeObstacles); }); };

// --- Section Check Logic and Drawing ---
    const woodAllowableStresses = { "Sugi": { name: "杉", fc: [7.2, 14.4], ft: [5.4, 10.8], fb: [7.8, 15.6], fs: [0.7, 1.4] }, "Hinoki": { name: "檜", fc: [9.6, 19.2], ft: [7.8, 15.6], fb: [10.8, 21.6], fs: [0.9, 1.8] }, "Matsu": { name: "松", fc: [9.0, 18.0], ft: [6.6, 13.2], fb: [9.6, 19.2], fs: [0.9, 1.8] } };
    const calculateSectionCheck = (loadTerm) => {
        if (!lastResults) return [];
        const { members, forces, memberLoads } = lastResults;
        const results = [];
        members.forEach((member, idx) => {
            const { strengthProps, A, Z, ix, iy, E, length } = member;
            if(!strengthProps || !A || !Z || isNaN(A) || isNaN(Z)) {
                results.push({ maxRatio: 'N/A', N: 0, M: 0, checkType: 'データ不足', status: 'error', ratios: Array(21).fill(0)});
                return;
            }
            let ft, fc, fb, fs;
            const termIndex = (loadTerm === 'long') ? 0 : 1;
            switch(strengthProps.type) {
                case 'F-value': case 'F-stainless': case 'F-aluminum':
                    const F = strengthProps.value;
                    if (!F || isNaN(F)) { results.push({ maxRatio: 'N/A', N: 0, M: 0, checkType: 'F値無効', status: 'error', ratios: Array(21).fill(0)}); return; }
                    const factor = (loadTerm === 'long') ? 1.5 : 1.0;
                    ft = F / factor; fb = F / factor; fs = F / (factor * Math.sqrt(3));
                    const lk = length, i_min = Math.min(ix, iy);
                    fc = ft;
                    if (i_min > 1e-9) {
                        const lambda = lk / i_min, E_n_mm2 = E * 1e-3;
                        const lambda_p = Math.PI * Math.sqrt(E_n_mm2 / (0.6 * F));
                        if (lambda <= lambda_p) { fc = (1 - 0.4 * (lambda / lambda_p)**2) * F / factor; } 
                        else { fc = (0.277 * F) / ((lambda / lambda_p)**2); }
                    }
                    break;
                case 'wood-type':
                    const woodType = strengthProps.value;
                    const stresses = woodAllowableStresses[woodType];
                    if (!stresses) { results.push({ maxRatio: 'N/A', N: 0, M: 0, checkType: '木材データ無', status: 'error', ratios: Array(21).fill(0)}); return; }
                    ft = stresses.ft[termIndex]; fc = stresses.fc[termIndex]; fb = stresses.fb[termIndex]; fs = stresses.fs[termIndex];
                    break;
                case 'Fc':
                default:
                    results.push({ maxRatio: 'N/A', N: 0, M: 0, checkType: '未対応材料', status: 'error', ratios: Array(21).fill(0)});
                    return;
            }
            const force = forces[idx], load = memberLoads.find(l => l.memberIndex === idx), w = load ? load.w : 0;
            const L = length, N = -force.N_i, Z_mm3 = Z * 1e9, A_mm2 = A * 1e6;
            let maxRatio = 0, M_at_max = 0;
            const ratios = [];
            for (let k = 0; k <= 20; k++) {
                const x = (k / 20) * L, M_linear = -force.M_i * (1 - x/L) + force.M_j * (x/L), M_parabolic = w * L * x / 2 - w * x**2 / 2;
                const M_x = M_linear + M_parabolic, sigma_a = (N * 1000) / A_mm2, sigma_b = (Math.abs(M_x) * 1e6) / Z_mm3;
                let ratio_x = 0;
                if(isNaN(sigma_a) || isNaN(sigma_b)) { ratio_x = Infinity; }
                else if (sigma_a >= 0) { ratio_x = (sigma_a / ft) + (sigma_b / fb); } 
                else { ratio_x = (Math.abs(sigma_a) / fc) + (sigma_b / fb); }
                ratios.push(ratio_x);
                if (ratio_x > maxRatio) { maxRatio = ratio_x; M_at_max = M_x; }
            }
            results.push({ maxRatio, N, M: M_at_max, checkType: '組合せ応力', status: maxRatio > 1.0 ? 'NG' : 'OK', ratios });
        });
        return results;
    };

    const displaySectionCheckResults = () => {
        if (!lastSectionCheckResults) { elements.sectionCheckResults.innerHTML = ''; return; }
        console.log("断面算定の計算結果:", lastSectionCheckResults);
        let html = `<thead><tr><th>部材 #</th><th>軸力 N (kN)</th><th>曲げ M (kN·m)</th><th>検定項目</th><th>検定比 (D/C)</th><th>判定</th><th>詳細</th></tr></thead><tbody>`;
        lastSectionCheckResults.forEach((res, i) => {
            const is_ng = res.status === 'NG';
            const maxRatioText = (typeof res.maxRatio === 'number' && isFinite(res.maxRatio)) ? res.maxRatio.toFixed(2) : res.maxRatio;
            const statusText = is_ng ? '❌ NG' : '✅ OK';
            html += `<tr ${is_ng ? 'style="background-color: #fdd;"' : ''}><td>${i + 1}</td><td>${res.N.toFixed(2)}</td><td>${res.M.toFixed(2)}</td><td>${res.checkType}</td><td style="font-weight: bold; ${is_ng ? 'color: red;' : ''}">${maxRatioText}</td><td>${statusText}</td><td><button onclick="showSectionCheckDetail(${i})">詳細</button></td></tr>`;
        });
        html += `</tbody>`;
        elements.sectionCheckResults.innerHTML = html;
    };

    const showSectionCheckDetail = (memberIndex) => {
        const res = lastSectionCheckResults[memberIndex];
        if (!res || !res.ratios) return;

        const { members, forces, memberLoads } = lastResults;
        const member = members[memberIndex];
        const force = forces[memberIndex];
        const load = memberLoads.find(l => l.memberIndex === memberIndex);
        const w = load ? load.w : 0;
        const L = member.length;
        const numPoints = res.ratios.length;

        // 材料特性の取得
        const { strengthProps, A, Z, ix, iy, E } = member;
        let materialInfo = '';
        let allowableStresses = { ft: 0, fc: 0, fb: 0, fs: 0 };
        
        const selectedTerm = document.querySelector('input[name="load-term"]:checked').value;
        const termIndex = (selectedTerm === 'long') ? 0 : 1;
        
        switch(strengthProps.type) {
            case 'F-value':
            case 'F-stainless':
            case 'F-aluminum':
                const F = strengthProps.value;
                const factor = (selectedTerm === 'long') ? 1.5 : 1.0;
                materialInfo = `材料: ${strengthProps.type === 'F-value' ? '鋼材' : strengthProps.type === 'F-stainless' ? 'ステンレス' : 'アルミニウム'} (F=${F} N/mm²)`;
                allowableStresses.ft = F / factor;
                allowableStresses.fb = F / factor;
                allowableStresses.fs = F / (factor * Math.sqrt(3));
                
                // 座屈を考慮した圧縮許容応力度
                const lk = L, i_min = Math.min(ix, iy);
                allowableStresses.fc = allowableStresses.ft;
                if (i_min > 1e-9) {
                    const lambda = lk / i_min, E_n_mm2 = E * 1e-3;
                    const lambda_p = Math.PI * Math.sqrt(E_n_mm2 / (0.6 * F));
                    if (lambda <= lambda_p) {
                        allowableStresses.fc = (1 - 0.4 * (lambda / lambda_p)**2) * F / factor;
                    } else {
                        allowableStresses.fc = (0.277 * F) / ((lambda / lambda_p)**2);
                    }
                }
                break;
            case 'wood-type':
                const woodType = strengthProps.value;
                const stresses = woodAllowableStresses[woodType];
                materialInfo = `材料: 木材 (${stresses.name})`;
                allowableStresses.ft = stresses.ft[termIndex];
                allowableStresses.fc = stresses.fc[termIndex];
                allowableStresses.fb = stresses.fb[termIndex];
                allowableStresses.fs = stresses.fs[termIndex];
                break;
            default:
                materialInfo = '材料: 不明';
        }

        let detailHtml = `
            <div style="font-family: Arial, sans-serif;">
                <h3>部材 ${memberIndex + 1} の詳細応力度計算結果</h3>
                <div style="margin-bottom: 20px; padding: 10px; background-color: #f5f5f5; border-radius: 5px;">
                    <h4>部材情報</h4>
                    <p><strong>${materialInfo}</strong></p>
                    <p>部材長: ${L.toFixed(2)} m</p>
                    <p>断面積 A: ${(A * 1e4).toFixed(2)} cm²</p>
                    <p>断面係数 Z: ${(Z * 1e6).toFixed(2)} cm³</p>
                    <p>回転半径 ix: ${(ix * 1e2).toFixed(2)} cm, iy: ${(iy * 1e2).toFixed(2)} cm</p>
                    ${w !== 0 ? `<p>等分布荷重: ${w} kN/m</p>` : ''}
                </div>
                <div style="margin-bottom: 20px; padding: 10px; background-color: #e8f4fd; border-radius: 5px;">
                    <h4>許容応力度 (${selectedTerm === 'long' ? '長期' : '短期'})</h4>
                    <p>引張許容応力度 ft: ${allowableStresses.ft.toFixed(2)} N/mm²</p>
                    <p>圧縮許容応力度 fc: ${allowableStresses.fc.toFixed(2)} N/mm²</p>
                    <p>曲げ許容応力度 fb: ${allowableStresses.fb.toFixed(2)} N/mm²</p>
                    <p>せん断許容応力度 fs: ${allowableStresses.fs.toFixed(2)} N/mm²</p>
                </div>
                <div style="margin-bottom: 20px; padding: 10px; background-color: #fff2e8; border-radius: 5px;">
                    <h4>部材端力</h4>
                    <p>i端: N = ${(-force.N_i).toFixed(2)} kN, Q = ${force.Q_i.toFixed(2)} kN, M = ${force.M_i.toFixed(2)} kN·m</p>
                    <p>j端: N = ${force.N_j.toFixed(2)} kN, Q = ${(-force.Q_j).toFixed(2)} kN, M = ${force.M_j.toFixed(2)} kN·m</p>
                </div>
                <table style="width: 100%; border-collapse: collapse; margin-top: 10px;">
                    <thead>
                        <tr style="background-color: #f0f0f0;">
                            <th style="border: 1px solid #ccc; padding: 8px;">位置 (m)</th>
                            <th style="border: 1px solid #ccc; padding: 8px;">軸力 N (kN)</th>
                            <th style="border: 1px solid #ccc; padding: 8px;">曲げ M (kN·m)</th>
                            <th style="border: 1px solid #ccc; padding: 8px;">軸応力度 σ_a (N/mm²)</th>
                            <th style="border: 1px solid #ccc; padding: 8px;">曲げ応力度 σ_b (N/mm²)</th>
                            <th style="border: 1px solid #ccc; padding: 8px;">検定比 (D/C)</th>
                            <th style="border: 1px solid #ccc; padding: 8px;">判定</th>
                        </tr>
                    </thead>
                    <tbody>`;

        for (let k = 0; k < numPoints; k++) {
            const x = (k / (numPoints - 1)) * L;
            const ratio = res.ratios[k];
            
            // 実際の曲げモーメント計算（等分布荷重を考慮）
            const M_linear = -force.M_i * (1 - x/L) + force.M_j * (x/L);
            const M_parabolic = w * L * x / 2 - w * x**2 / 2;
            const M_x = M_linear + M_parabolic;
            
            const N = -force.N_i; // 軸力は部材全体で一定
            const sigma_a = (N * 1000) / (A * 1e6);
            const sigma_b = (Math.abs(M_x) * 1e6) / (Z * 1e9);
            
            const status = ratio > 1.0 ? '❌ NG' : '✅ OK';
            const rowStyle = ratio > 1.0 ? 'background-color: #fdd;' : '';
            
            detailHtml += `
                <tr style="${rowStyle}">
                    <td style="border: 1px solid #ccc; padding: 8px; text-align: center;">${x.toFixed(2)}</td>
                    <td style="border: 1px solid #ccc; padding: 8px; text-align: center;">${N.toFixed(2)}</td>
                    <td style="border: 1px solid #ccc; padding: 8px; text-align: center;">${M_x.toFixed(2)}</td>
                    <td style="border: 1px solid #ccc; padding: 8px; text-align: center;">${sigma_a.toFixed(2)}</td>
                    <td style="border: 1px solid #ccc; padding: 8px; text-align: center;">${sigma_b.toFixed(2)}</td>
                    <td style="border: 1px solid #ccc; padding: 8px; text-align: center; font-weight: bold;">${ratio.toFixed(3)}</td>
                    <td style="border: 1px solid #ccc; padding: 8px; text-align: center;">${status}</td>
                </tr>`;
        }

        detailHtml += `
                    </tbody>
                </table>
                <div style="margin-top: 20px; padding: 10px; background-color: #f9f9f9; border-radius: 5px;">
                    <h4>検定式</h4>
                    <p>軸力が引張の場合: D/C = σ_a/ft + σ_b/fb</p>
                    <p>軸力が圧縮の場合: D/C = σ_a/fc + σ_b/fb</p>
                    <p>※ σ_a = N/A, σ_b = |M|/Z</p>
                </div>
            </div>`;

        // ポップアップで表示
        const popup = document.createElement('div');
        popup.style.position = 'fixed';
        popup.style.top = '50%';
        popup.style.left = '50%';
        popup.style.transform = 'translate(-50%, -50%)';
        popup.style.background = 'white';
        popup.style.border = '2px solid #ccc';
        popup.style.borderRadius = '10px';
        popup.style.padding = '20px';
        popup.style.zIndex = '1000';
        popup.style.maxHeight = '90vh';
        popup.style.maxWidth = '90vw';
        popup.style.overflowY = 'auto';
        popup.style.boxShadow = '0 4px 20px rgba(0,0,0,0.3)';
        
        const closeButton = document.createElement('button');
        closeButton.textContent = '閉じる';
        closeButton.style.marginTop = '20px';
        closeButton.style.padding = '10px 20px';
        closeButton.style.backgroundColor = '#007bff';
        closeButton.style.color = 'white';
        closeButton.style.border = 'none';
        closeButton.style.borderRadius = '5px';
        closeButton.style.cursor = 'pointer';
        closeButton.onclick = () => popup.remove();
        
        popup.innerHTML = detailHtml;
        popup.appendChild(closeButton);
        document.body.appendChild(popup);
    };

    // グローバルスコープに関数を公開
    window.showSectionCheckDetail = showSectionCheckDetail;

    const drawRatioDiagram = () => {
        const drawingCtx = getDrawingContext(elements.ratioCanvas);
        if (!drawingCtx || !lastResults || !lastSectionCheckResults) return;
        const { ctx, transform, scale } = drawingCtx;
        const { nodes, members } = lastResults;
        drawStructure(ctx, transform, nodes, members, '#ccc', false);
        const labelManager = LabelManager();
        const nodeObstacles = nodes.map(n => { const pos = transform(n.x, n.y); return {x1: pos.x - 12, y1: pos.y - 12, x2: pos.x + 12, y2: pos.y + 12}; });
        const maxOffsetPixels = 60, ratioScale = maxOffsetPixels / (scale * 2.0);
        members.forEach((m, idx) => {
            const res = lastSectionCheckResults[idx];
            if(res.status === 'error') return;
            const n_i = nodes[m.i], n_j = nodes[m.j];
            if (res.maxRatio > 1.0) {
                 ctx.beginPath();
                 const start = transform(n_i.x, n_i.y), end = transform(n_j.x, n_j.y);
                 ctx.moveTo(start.x, start.y);
                 for (let k = 0; k <= 20; k++) {
                    const ratio = res.ratios[k], offset = -ratio * ratioScale, x_local = (k/20) * m.length;
                    const globalX = n_i.x + x_local * m.c - offset * m.s, globalY = n_i.y + x_local * m.s + offset * m.c;
                    ctx.lineTo(transform(globalX, globalY).x, transform(globalX, globalY).y);
                 }
                 ctx.lineTo(end.x, end.y);
                 ctx.fillStyle = 'rgba(255, 0, 0, 0.3)'; ctx.strokeStyle = 'red'; ctx.lineWidth = 1; ctx.closePath(); ctx.fill(); ctx.stroke();
            }
            ctx.beginPath();
            const start = transform(n_i.x, n_i.y);
            ctx.moveTo(start.x, start.y);
            for (let k = 0; k <= 20; k++) {
                const ratio = Math.min(res.ratios[k], 1.0), offset = -ratio * ratioScale, x_local = (k/20) * m.length;
                const globalX = n_i.x + x_local * m.c - offset * m.s, globalY = n_i.y + x_local * m.s + offset * m.c;
                ctx.lineTo(transform(globalX, globalY).x, transform(globalX, globalY).y);
            }
            const end = transform(n_j.x, n_j.y);
            ctx.lineTo(end.x, end.y);
            ctx.fillStyle = 'rgba(0,0,255,0.2)'; ctx.strokeStyle = 'blue'; ctx.lineWidth = 1; ctx.closePath(); ctx.fill(); ctx.stroke();
            ctx.beginPath();
            const offset_1 = -1.0 * ratioScale;
            const p1_offset_x = -offset_1 * m.s, p1_offset_y = offset_1 * m.c;
            const p1 = transform(n_i.x+p1_offset_x, n_i.y+p1_offset_y), p2 = transform(n_j.x+p1_offset_x, n_j.y+p1_offset_y);
            ctx.moveTo(p1.x, p1.y); ctx.lineTo(p2.x, p2.y);
            ctx.strokeStyle = 'rgba(0,0,0,0.5)'; ctx.setLineDash([5, 5]); ctx.stroke(); ctx.setLineDash([]);
            ctx.fillStyle = res.maxRatio > 1.0 ? 'red' : '#333';
            const mid_offset = -res.maxRatio * ratioScale * 0.5;
            const mid_offset_x = -mid_offset*m.s, mid_offset_y = mid_offset*m.c;
            const mid_pos = transform((n_i.x+n_j.x)/2+mid_offset_x, (n_i.y+n_j.y)/2+mid_offset_y);
            labelManager.draw(ctx, res.maxRatio.toFixed(2), mid_pos.x, mid_pos.y, nodeObstacles);
        });

        // 部材番号を表示
        ctx.fillStyle = '#0066cc';
        ctx.font = 'bold 14px Arial';
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        members.forEach((m, idx) => {
            const n_i = nodes[m.i], n_j = nodes[m.j];
            const mid_x = (n_i.x + n_j.x) / 2;
            const mid_y = (n_i.y + n_j.y) / 2;
            const mid_pos = transform(mid_x, mid_y);

            // 部材番号の背景を描画（視認性向上のため）
            const text = `${idx + 1}`;
            const textWidth = ctx.measureText(text).width;
            const textHeight = 14;
            ctx.fillStyle = 'rgba(255, 255, 255, 0.9)';
            ctx.fillRect(mid_pos.x - textWidth/2 - 4, mid_pos.y - textHeight/2 - 2, textWidth + 8, textHeight + 4);

            // 部材番号を描画
            ctx.fillStyle = '#0066cc';
            ctx.fillText(text, mid_pos.x, mid_pos.y);
        });
    };
    const zoom = (factor, centerX, centerY) => {
        if (!panZoomState.isInitialized) return;
        const { scale, offsetX, offsetY } = panZoomState;
        const modelX = (centerX - offsetX) / scale;
        const modelY = (offsetY - centerY) / scale;
        const newScale = scale * factor;
        panZoomState.scale = newScale;
        panZoomState.offsetX = centerX - modelX * newScale;
        panZoomState.offsetY = centerY + modelY * newScale;
        drawOnCanvas();
    };

    const animateDisplacement = (nodes, members, D_global, memberLoads) => {
        const drawingCtx = getDrawingContext(elements.modelCanvas);
        if (!drawingCtx) return;
        const { ctx, transform, scale } = drawingCtx;

        let dispScale = parseFloat(elements.animScaleInput.value);

        if (isNaN(dispScale)) {
            dispScale = lastDisplacementScale || 0;
            elements.animScaleInput.placeholder = `自動(${dispScale.toFixed(2)})`;
        }
        
        const duration = 2000;
        let startTime = null;

        const animationFrame = (timestamp) => {
            if (!startTime) startTime = timestamp;
            const elapsedTime = timestamp - startTime;
            let progress = Math.min(elapsedTime / duration, 1);
            progress = progress < 0.5 ? 4 * progress * progress * progress : 1 - Math.pow(-2 * progress + 2, 3) / 2;

            const currentDrawingCtx = getDrawingContext(elements.modelCanvas);
            if (!currentDrawingCtx) return;
            
            const { ctx, transform } = currentDrawingCtx;
            if (elements.gridToggle.checked) { drawGrid(ctx, transform, elements.modelCanvas.clientWidth, elements.modelCanvas.clientHeight); }
            drawStructure(ctx, transform, nodes, members, '#ccc', true);
            drawBoundaryConditions(ctx, transform, nodes);
            
            ctx.strokeStyle = 'red';
            ctx.lineWidth = 2;
            members.forEach((m, idx) => {
                const L = m.length, c = m.c, s = m.s, ni = nodes[m.i];
                const d_global_member_vec = [ ...D_global.slice(m.i * 3, m.i * 3 + 3), ...D_global.slice(m.j * 3, m.j * 3 + 3) ];
                const d_local_vec = mat.multiply(m.T, d_global_member_vec);
                const [ui, vi, thi, uj, vj, thj] = d_local_vec.map(v => v[0]);
                const load = memberLoads.find(l => l.memberIndex === idx), w = load ? load.w : 0, E = m.E, I = m.I;
                ctx.beginPath();
                for (let k = 0; k <= 20; k++) {
                    const x = (k / 20) * L, xi = x / L;
                    const N1 = 1 - 3*xi**2 + 2*xi**3, N2 = x * (1 - xi)**2, N3 = 3*xi**2 - 2*xi**3, N4 = (x**2 / L) * (xi - 1);
                    const u_local = (1 - xi) * ui + xi * uj, v_homogeneous = N1*vi + N2*thi + N3*vj + N4*thj;
                    let v_particular = 0;
                    if (w !== 0 && E > 0 && I > 0) {
                        if (m.i_conn === 'rigid' && m.j_conn === 'rigid') v_particular = (w * x**2 * (L - x)**2) / (24 * E * I);
                        else if (m.i_conn === 'pinned' && m.j_conn === 'pinned') v_particular = (w * x * (L**3 - 2 * L * x**2 + x**3)) / (24 * E * I);
                        else if (m.i_conn === 'rigid' && m.j_conn === 'pinned') v_particular = (w * x**2 * (3 * L**2 - 5 * L * x + 2 * x**2)) / (48 * E * I);
                        else if (m.i_conn === 'pinned' && m.j_conn === 'rigid') v_particular = (w * x * (L**3 - 3 * L * x**2 + 2 * x**3)) / (48 * E * I);
                    }
                    const v_local = v_homogeneous - v_particular;
                    const p_deformed = { x: ni.x + (x*c - (v_local*dispScale*progress)*s) + (u_local*dispScale*progress*c), y: ni.y + (x*s + (v_local*dispScale*progress)*c) + (u_local*dispScale*progress*s) };
                    const p = transform(p_deformed.x, p_deformed.y);
                    if (k === 0) ctx.moveTo(p.x, p.y); else ctx.lineTo(p.x, p.y);
                }
                ctx.stroke();
            });

            if (progress < 1) { requestAnimationFrame(animationFrame); } 
            else { drawOnCanvas(); }
        };
        requestAnimationFrame(animationFrame);
    };

    // --- Canvas Interaction ---
    const inverseTransform = (mouseX, mouseY) => { if (!lastDrawingContext) return null; const { scale, offsetX, offsetY } = lastDrawingContext; const modelX = (mouseX - offsetX) / scale; const modelY = (mouseY - offsetY) / -scale; return { x: modelX, y: modelY }; };
    const getNodeAt = (canvasX, canvasY) => { if (!lastDrawingContext) return -1; try { const { nodes } = parseInputs(); const tolerance = 10; for (let i = 0; i < nodes.length; i++) { const nodePos = lastDrawingContext.transform(nodes[i].x, nodes[i].y); const dist = Math.sqrt((canvasX - nodePos.x)**2 + (canvasY - nodePos.y)**2); if (dist < tolerance) return i; } } catch(e) {} return -1; };
    const getMemberAt = (canvasX, canvasY) => { if (!lastDrawingContext) return -1; try { const { nodes, members } = parseInputs(); const tolerance = 5; for (let i = 0; i < members.length; i++) { const member = members[i]; const p1 = lastDrawingContext.transform(nodes[member.i].x, nodes[member.i].y), p2 = lastDrawingContext.transform(nodes[member.j].x, nodes[member.j].y); const dx = p2.x - p1.x, dy = p2.y - p1.y, lenSq = dx*dx + dy*dy; if (lenSq === 0) continue; let t = ((canvasX - p1.x) * dx + (canvasY - p1.y) * dy) / lenSq; t = Math.max(0, Math.min(1, t)); const closestX = p1.x + t * dx, closestY = p1.y + t * dy; const dist = Math.sqrt((canvasX - closestX)**2 + (canvasY - closestY)**2); if (dist < tolerance) return i; } } catch (e) {} return -1; };
    const setCanvasMode = (newMode) => { canvasMode = newMode; firstMemberNode = null; const kebabCaseMode = newMode.replace(/[A-Z]/g, letter => `-${letter.toLowerCase()}`); document.querySelectorAll('.mode-btn').forEach(btn => btn.classList.remove('active')); document.getElementById(`mode-${kebabCaseMode}`).classList.add('active'); elements.modelCanvas.style.cursor = { select: 'default', addNode: 'crosshair', addMember: 'copy' }[newMode]; };

    elements.zoomInBtn.onclick = () => {
        const rect = elements.modelCanvas.getBoundingClientRect();
        zoom(1.2, rect.width / 2, rect.height / 2);
    };
    elements.zoomOutBtn.onclick = () => {
        const rect = elements.modelCanvas.getBoundingClientRect();
        zoom(1 / 1.2, rect.width / 2, rect.height / 2);
    };
    elements.modelCanvas.addEventListener('wheel', (e) => {
        e.preventDefault();
        const rect = elements.modelCanvas.getBoundingClientRect();
        const mouseX = e.clientX - rect.left;
        const mouseY = e.clientY - rect.top;
        const zoomFactor = e.deltaY < 0 ? 1.1 : 1 / 1.1;
        zoom(zoomFactor, mouseX, mouseY);
    }, { passive: false });
    
    elements.membersTable.addEventListener('click', (e) => {
    if (e.target && e.target.classList.contains('select-props-btn')) {
        const row = e.target.closest('tr');
        if (row) {
            const memberIndex = Array.from(row.parentNode.children).indexOf(row);
            
            // 材料情報を取得して渡す
            const eSelect = row.cells[3].querySelector('select');
            const selectedOption = eSelect.options[eSelect.selectedIndex];
            let materialType = 'steel'; // デフォルト
            if (selectedOption.textContent.includes('木材')) materialType = 'wood';
            else if (selectedOption.textContent.includes('コンクリート')) materialType = 'concrete';
            else if (selectedOption.textContent.includes('ステンレス')) materialType = 'stainless';
            else if (selectedOption.textContent.includes('アルミニウム')) materialType = 'aluminum';

            const strengthInputContainer = row.cells[4].firstElementChild;
            let strengthValue = '';
            if (strengthInputContainer.querySelector('input')) strengthValue = strengthInputContainer.querySelector('input').value;
            if (strengthInputContainer.querySelector('select')) strengthValue = strengthInputContainer.querySelector('select').value;
            
            openSteelSelector(memberIndex, {
                material: materialType,
                E: eSelect.value === 'custom' ? row.cells[3].querySelector('input[type="number"]').value : eSelect.value,
                strengthValue: strengthValue
            });
        }
    }
});

    elements.modeSelectBtn.onclick = () => setCanvasMode('select');
    elements.modeAddNodeBtn.onclick = () => setCanvasMode('addNode');
    elements.modeAddMemberBtn.onclick = () => {
        document.getElementById('add-popup-e-container').innerHTML = createEInputHTML('add-popup-e', newMemberDefaults.E);
        document.getElementById('add-popup-f-container').innerHTML = createStrengthInputHTML('steel', 'add-popup-f', newMemberDefaults.F);
        document.getElementById('add-popup-i').value = newMemberDefaults.I;
        document.getElementById('add-popup-a').value = newMemberDefaults.A;
        document.getElementById('add-popup-z').value = newMemberDefaults.Z;
        document.getElementById('add-popup-i-conn').value = newMemberDefaults.i_conn;
        document.getElementById('add-popup-j-conn').value = newMemberDefaults.j_conn;
        const btnRect = elements.modeAddMemberBtn.getBoundingClientRect();
        elements.addMemberPopup.style.left = `${btnRect.left}px`;
        elements.addMemberPopup.style.top = `${btnRect.bottom + 5}px`;
        elements.addMemberPopup.style.display = 'block';
    };
    document.getElementById('add-popup-ok').onclick = () => {
        const e_select = document.getElementById('add-popup-e-select'), e_input = document.getElementById('add-popup-e-input');
        newMemberDefaults.E = e_select.value === 'custom' ? e_input.value : e_select.value;
        const f_select = document.getElementById('add-popup-f-select'), f_input = document.getElementById('add-popup-f-input');
        newMemberDefaults.F = f_select.value === 'custom' ? f_input.value : f_select.value;
        newMemberDefaults.I = document.getElementById('add-popup-i').value;
        newMemberDefaults.A = document.getElementById('add-popup-a').value;
        newMemberDefaults.Z = document.getElementById('add-popup-z').value;
        newMemberDefaults.i_conn = document.getElementById('add-popup-i-conn').value;
        newMemberDefaults.j_conn = document.getElementById('add-popup-j-conn').value;
        elements.addMemberPopup.style.display = 'none';
        setCanvasMode('addMember');
    };
    document.getElementById('add-popup-cancel').onclick = () => { elements.addMemberPopup.style.display = 'none'; };

    elements.modelCanvas.addEventListener('mousedown', (e) => {
        if (e.button !== 0) return;
        const rect = elements.modelCanvas.getBoundingClientRect();
        const mouseX = e.clientX - rect.left;
        const mouseY = e.clientY - rect.top;
        selectedNodeIndex = getNodeAt(mouseX, mouseY);
        if (canvasMode === 'select' && selectedNodeIndex !== -1) {
            isDragging = true;
            pushState();
        } else if (canvasMode === 'select') {
            isDraggingCanvas = true;
            lastMouseX = mouseX;
            lastMouseY = mouseY;
        }
    });
    elements.modelCanvas.addEventListener('mousemove', (e) => {
        if (isDragging && canvasMode === 'select' && selectedNodeIndex !== null) {
            const rect = elements.modelCanvas.getBoundingClientRect();
            let mouseX = e.clientX - rect.left, mouseY = e.clientY - rect.top;
            let modelCoords = inverseTransform(mouseX, mouseY);
            if (modelCoords) {
                if (elements.gridToggle.checked) {
                    const spacing = parseFloat(elements.gridSpacing.value);
                    modelCoords.x = Math.round(modelCoords.x / spacing) * spacing;
                    modelCoords.y = Math.round(modelCoords.y / spacing) * spacing;
                }
                const nodeRow = elements.nodesTable.rows[selectedNodeIndex];
                nodeRow.cells[1].querySelector('input').value = modelCoords.x.toFixed(2);
                nodeRow.cells[2].querySelector('input').value = modelCoords.y.toFixed(2);
                drawOnCanvas();
            }
        } else if (isDraggingCanvas && canvasMode === 'select') {
            const rect = elements.modelCanvas.getBoundingClientRect();
            const mouseX = e.clientX - rect.left;
            const mouseY = e.clientY - rect.top;
            const deltaX = mouseX - lastMouseX;
            const deltaY = mouseY - lastMouseY;
            panZoomState.offsetX += deltaX;
            panZoomState.offsetY += deltaY;
            lastMouseX = mouseX;
            lastMouseY = mouseY;
            drawOnCanvas();
        }
    });
    window.addEventListener('mouseup', (e) => {
        if (e.button === 0) {
            if (isDragging) {
                elements.nodesTable.rows[selectedNodeIndex]?.cells[1].querySelector('input').dispatchEvent(new Event('change'));
                isDragging = false;
            }
            if (isDraggingCanvas) {
                isDraggingCanvas = false;
            }
        }
    });
    elements.modelCanvas.addEventListener('click', (e) => { 
        const rect = elements.modelCanvas.getBoundingClientRect(); let mouseX = e.clientX - rect.left, mouseY = e.clientY - rect.top; const clickedNodeIndex = getNodeAt(mouseX, mouseY); 
        if (canvasMode === 'addNode') {
            const targetMemberIndex = getMemberAt(mouseX, mouseY);
            let modelCoords = inverseTransform(mouseX, mouseY); if (!modelCoords) return;
            if (targetMemberIndex !== -1) {
                pushState();
                const { nodes } = parseInputs(), memberRow = elements.membersTable.rows[targetMemberIndex];
                const startNodeId = parseInt(memberRow.cells[1].querySelector('input').value), endNodeId = parseInt(memberRow.cells[2].querySelector('input').value);
                const p1 = nodes[startNodeId - 1], p2 = nodes[endNodeId - 1];
                let finalCoords;
                if (elements.gridToggle.checked) {
                    const spacing = parseFloat(elements.gridSpacing.value), snapTolerance = spacing / 2.5;
                    const nearestGridX = Math.round(modelCoords.x / spacing) * spacing, nearestGridY = Math.round(modelCoords.y / spacing) * spacing;
                    const distToGrid = Math.sqrt((modelCoords.x - nearestGridX)**2 + (modelCoords.y - nearestGridY)**2);
                    if (distToGrid < snapTolerance) {
                        const isCollinear = Math.abs((nearestGridY - p1.y)*(p2.x - p1.x) - (nearestGridX - p1.x)*(p2.y - p1.y)) < 1e-6;
                        const isWithinBounds = (nearestGridX >= Math.min(p1.x,p2.x)-1e-6 && nearestGridX <= Math.max(p1.x,p2.x)+1e-6 && nearestGridY >= Math.min(p1.y,p2.y)-1e-6 && nearestGridY <= Math.max(p1.y,p2.y)+1e-6);
                        if (isCollinear && isWithinBounds) finalCoords = { x: nearestGridX, y: nearestGridY };
                    }
                }
                if (!finalCoords) { const dx = p2.x-p1.x, dy = p2.y-p1.y, lenSq = dx*dx+dy*dy, t = lenSq===0 ? 0 : ((modelCoords.x-p1.x)*dx + (modelCoords.y-p1.y)*dy)/lenSq; const clampedT=Math.max(0,Math.min(1,t)); finalCoords={x:p1.x+clampedT*dx,y:p1.y+clampedT*dy}; }
                const e_select=memberRow.cells[3].querySelector('select'), e_input=memberRow.cells[3].querySelector('input[type="number"]'); const E_val = e_select.value==='custom'?e_input.value:e_select.value;
                const f_select=memberRow.cells[4].querySelector('select'), f_input=memberRow.cells[4].querySelector('input[type="number"]'); const F_val = f_select ? (f_select.value==='custom'?f_input.value:f_select.value) : '235';
                const I_m4 = parseFloat(memberRow.cells[5].querySelector('input').value)*1e-8, A_m2 = parseFloat(memberRow.cells[6].querySelector('input').value)*1e-4, Z_m3 = parseFloat(memberRow.cells[7].querySelector('input').value)*1e-6;
                const props = {E:E_val, F:F_val, I:I_m4, A:A_m2, Z:Z_m3, i_conn:memberRow.cells[9].querySelector('select').value, j_conn:memberRow.cells[10].querySelector('select').value};
                memberRow.querySelector('.delete-row-btn').onclick.apply(memberRow.querySelector('.delete-row-btn'));
                addRow(elements.nodesTable, [`#`,`<input type="number" value="${finalCoords.x.toFixed(2)}">`,`<input type="number" value="${finalCoords.y.toFixed(2)}">`,`<select><option value="free" selected>自由</option><option value="pinned">ピン</option><option value="fixed">固定</option><option value="roller">ローラー</option></select>`], false);
                const newNodeId = elements.nodesTable.rows.length;
                addRow(elements.membersTable, [`#`, ...memberRowHTML(startNodeId, newNodeId, props.E, props.F, props.I, props.A, props.Z, props.i_conn, 'rigid')], false);
                addRow(elements.membersTable, [`#`, ...memberRowHTML(newNodeId, endNodeId, props.E, props.F, props.I, props.A, props.Z, 'rigid', props.j_conn)], false);
                renumberTables(); drawOnCanvas();
            } else { 
                const spacing=parseFloat(elements.gridSpacing.value), snapTolerance=spacing/2.5;
                const snappedX=Math.round(modelCoords.x/spacing)*spacing, snappedY=Math.round(modelCoords.y/spacing)*spacing;
                const dist=Math.sqrt((modelCoords.x-snappedX)**2+(modelCoords.y-snappedY)**2);
                if (elements.gridToggle.checked && dist < snapTolerance) { modelCoords.x=snappedX; modelCoords.y=snappedY; }
                addRow(elements.nodesTable, [`#`,`<input type="number" value="${modelCoords.x.toFixed(2)}">`,`<input type="number" value="${modelCoords.y.toFixed(2)}">`,`<select><option value="free" selected>自由</option><option value="pinned">ピン</option><option value="fixed">固定</option><option value="roller">ローラー</option></select>`]); 
            }
        } else if (canvasMode === 'addMember') { 
            if (clickedNodeIndex !== -1) { 
                if (firstMemberNode === null) { firstMemberNode = clickedNodeIndex; } 
                else { 
                    if (firstMemberNode !== clickedNodeIndex) { 
                        const I_m4 = parseFloat(newMemberDefaults.I)*1e-8, A_m2 = parseFloat(newMemberDefaults.A)*1e-4, Z_m3 = parseFloat(newMemberDefaults.Z)*1e-6;
                        addRow(elements.membersTable, [`#`, ...memberRowHTML(firstMemberNode+1, clickedNodeIndex+1, newMemberDefaults.E, newMemberDefaults.F, I_m4, A_m2, Z_m3, newMemberDefaults.i_conn, newMemberDefaults.j_conn)]); 
                    } 
                    firstMemberNode = null; 
                } 
                drawOnCanvas(); 
            } 
        } 
    });

    const getNodeLoadAt = (canvasX, canvasY) => { if (!lastDrawingContext) return -1; try { const { nodes, nodeLoads } = parseInputs(); const arrowSize = 10, loadScale = 3, tolerance = 5; for (const load of nodeLoads) { if (load.px===0&&load.py===0&&load.mz===0) continue; const node=nodes[load.nodeIndex], pos=lastDrawingContext.transform(node.x, node.y); if (load.px!==0) { const dir=Math.sign(load.px), x1=pos.x, x2=pos.x-arrowSize*loadScale*dir; const rect={left:Math.min(x1,x2)-tolerance,right:Math.max(x1,x2)+tolerance,top:pos.y-(arrowSize/2)-tolerance,bottom:pos.y+(arrowSize/2)+tolerance}; if (canvasX>=rect.left&&canvasX<=rect.right&&canvasY>=rect.top&&canvasY<=rect.bottom) return load.nodeIndex; } if (load.py!==0) { const dir=Math.sign(load.py), y1=pos.y, y2=pos.y+arrowSize*loadScale*dir; const rect={top:Math.min(y1,y2)-tolerance,bottom:Math.max(y1,y2)+tolerance,left:pos.x-(arrowSize/2)-tolerance,right:pos.x+(arrowSize/2)+tolerance}; if (canvasX>=rect.left&&canvasX<=rect.right&&canvasY>=rect.top&&canvasY<=rect.bottom) return load.nodeIndex; } if (load.mz!==0) { const radius=arrowSize*1.5, dist=Math.sqrt((canvasX-pos.x)**2+(canvasY-pos.y)**2); if (dist>=radius-tolerance&&dist<=radius+tolerance) return load.nodeIndex; } } } catch (e) {} return -1; };

    elements.modelCanvas.addEventListener('contextmenu', (e) => {
        e.preventDefault();
        const rect = elements.modelCanvas.getBoundingClientRect(), mouseX = e.clientX-rect.left, mouseY = e.clientY-rect.top;
        elements.nodeContextMenu.style.display='none'; elements.memberPropsPopup.style.display='none'; elements.nodeLoadPopup.style.display='none'; elements.nodeCoordsPopup.style.display='none';
        selectedNodeIndex = getNodeAt(mouseX, mouseY);
        let loadedNodeIndex = -1; if (selectedNodeIndex === -1) { loadedNodeIndex = getNodeLoadAt(mouseX, mouseY); }
        selectedMemberIndex = getMemberAt(mouseX, mouseY);

        if (loadedNodeIndex !== -1) {
            selectedNodeIndex = loadedNodeIndex;
            const currentLoads = Array.from(elements.nodeLoadsTable.rows).find(row => parseInt(row.cells[0].querySelector('input').value)-1 === selectedNodeIndex);
            document.getElementById('popup-px').value=currentLoads?currentLoads.cells[1].querySelector('input').value:'0';
            document.getElementById('popup-py').value=currentLoads?currentLoads.cells[2].querySelector('input').value:'0';
            document.getElementById('popup-mz').value=currentLoads?currentLoads.cells[3].querySelector('input').value:'0';
            elements.nodeLoadPopup.style.left=`${e.pageX+10}px`; elements.nodeLoadPopup.style.top=`${e.pageY}px`; elements.nodeLoadPopup.style.display='block';
        } else if (selectedNodeIndex !== -1) {
            elements.nodeContextMenu.style.display='block'; elements.nodeContextMenu.style.left=`${e.pageX}px`; elements.nodeContextMenu.style.top=`${e.pageY}px`;
        } else if (selectedMemberIndex !== -1) {
            const memberRow = elements.membersTable.rows[selectedMemberIndex];
            const e_select=memberRow.cells[3].querySelector('select'), e_input=memberRow.cells[3].querySelector('input[type="number"]'); const currentE=(e_select.value==='custom')?e_input.value:e_select.value;
            document.getElementById('popup-e-container').innerHTML = createEInputHTML('popup-e', currentE);
            const strengthContainer = memberRow.cells[4].firstElementChild;
            const strengthType = strengthContainer.dataset.strengthType;
            let strengthValue;
            if (strengthContainer.querySelector('input')) strengthValue = strengthContainer.querySelector('input').value;
            if (strengthContainer.querySelector('select')) strengthValue = strengthContainer.querySelector('select').value;
            const selectedOption = e_select.options[e_select.selectedIndex];
            let materialType = 'steel';
            if (selectedOption.textContent.includes('木材')) materialType = 'wood';
            else if (selectedOption.textContent.includes('コンクリート')) materialType = 'concrete';
            else if (selectedOption.textContent.includes('ステンレス')) materialType = 'stainless';
            else if (selectedOption.textContent.includes('アルミニウム')) materialType = 'aluminum';
            document.getElementById('popup-f-container').innerHTML = createStrengthInputHTML(materialType, 'popup-f', strengthValue);
            document.getElementById('popup-i').value = memberRow.cells[5].querySelector('input').value;
            document.getElementById('popup-a').value = memberRow.cells[6].querySelector('input').value;
            document.getElementById('popup-z').value = memberRow.cells[7].querySelector('input').value;
            document.getElementById('popup-i-conn').value = memberRow.cells[9].querySelector('select').value;
            document.getElementById('popup-j-conn').value = memberRow.cells[10].querySelector('select').value;
            const memberLoadRow = Array.from(elements.memberLoadsTable.rows).find(row => parseInt(row.cells[0].querySelector('input').value)-1 === selectedMemberIndex);
            document.getElementById('popup-w').value = memberLoadRow ? memberLoadRow.cells[1].querySelector('input').value : '0';
            elements.memberPropsPopup.style.display='block'; elements.memberPropsPopup.style.left=`${e.pageX+10}px`; elements.memberPropsPopup.style.top=`${e.pageY}px`;
        }
    });

    document.addEventListener('click', (e) => { 
        if (elements.modeAddMemberBtn.contains(e.target)) return;
        if(!elements.memberPropsPopup.contains(e.target) && !elements.addMemberPopup.contains(e.target)) { elements.memberPropsPopup.style.display='none'; elements.addMemberPopup.style.display='none'; }
        if(!elements.nodeLoadPopup.contains(e.target)) elements.nodeLoadPopup.style.display='none';
        if(!elements.nodeCoordsPopup.contains(e.target)) elements.nodeCoordsPopup.style.display='none';
        if(!elements.nodeContextMenu.contains(e.target)) elements.nodeContextMenu.style.display='none';
    });

    elements.nodeContextMenu.addEventListener('click', (e) => {
        e.stopPropagation(); const target=e.target; if (selectedNodeIndex===null) return; const nodeRow=elements.nodesTable.rows[selectedNodeIndex];
        if (target.dataset.support) { pushState(); const selectEl=nodeRow.cells[3].querySelector('select'); selectEl.value=target.dataset.support; selectEl.dispatchEvent(new Event('change')); }
        if (target.id === 'menu-delete-node') { nodeRow.querySelector('.delete-row-btn').click(); }
        if (target.id === 'menu-add-load') {
            const currentLoads = Array.from(elements.nodeLoadsTable.rows).find(row => parseInt(row.cells[0].querySelector('input').value)-1 === selectedNodeIndex);
            document.getElementById('popup-px').value=currentLoads?currentLoads.cells[1].querySelector('input').value:'0';
            document.getElementById('popup-py').value=currentLoads?currentLoads.cells[2].querySelector('input').value:'0';
            document.getElementById('popup-mz').value=currentLoads?currentLoads.cells[3].querySelector('input').value:'0';
            elements.nodeLoadPopup.style.left=`${e.pageX+10}px`; elements.nodeLoadPopup.style.top=`${e.pageY}px`; elements.nodeLoadPopup.style.display='block';
        }
        if (target.id === 'menu-edit-coords') {
            document.getElementById('popup-x').value=nodeRow.cells[1].querySelector('input').value;
            document.getElementById('popup-y').value=nodeRow.cells[2].querySelector('input').value;
            elements.nodeCoordsPopup.style.left=`${e.pageX+10}px`; elements.nodeCoordsPopup.style.top=`${e.pageY}px`; elements.nodeCoordsPopup.style.display='block';
        }
        elements.nodeContextMenu.style.display='none';
    });

    document.getElementById('popup-select-section').onclick = () => {
    if (selectedMemberIndex !== null) {
        // ポップアップ内の情報から材料情報を取得
        const popup_e_select = document.getElementById('popup-e-select');
        const selectedOption = popup_e_select.options[popup_e_select.selectedIndex];
        let materialType = 'steel';
        if (selectedOption.textContent.includes('木材')) materialType = 'wood';
        else if (selectedOption.textContent.includes('コンクリート')) materialType = 'concrete';
        else if (selectedOption.textContent.includes('ステンレス')) materialType = 'stainless';
        else if (selectedOption.textContent.includes('アルミニウム')) materialType = 'aluminum';
        
        const strengthContainer = document.getElementById('popup-f-container').firstElementChild;
        let strengthValue = '';
        if (strengthContainer.querySelector('input')) strengthValue = strengthContainer.querySelector('input').value;
        if (strengthContainer.querySelector('select')) strengthValue = strengthContainer.querySelector('select').value;

        openSteelSelector(selectedMemberIndex, {
            material: materialType,
            E: popup_e_select.value === 'custom' ? document.getElementById('popup-e-input').value : popup_e_select.value,
            strengthValue: strengthValue
        });
        elements.memberPropsPopup.style.display = 'none';
    }
};

    document.getElementById('popup-save').onclick = () => {
        if(selectedMemberIndex === null) return; pushState();
        const memberRow = elements.membersTable.rows[selectedMemberIndex];
        const popup_e_select=document.getElementById('popup-e-select'), popup_e_input=document.getElementById('popup-e-input'); const newEValue=popup_e_select.value==='custom'?popup_e_input.value:popup_e_select.value;
        const table_e_select=memberRow.cells[3].querySelector('select'), table_e_input=memberRow.cells[3].querySelector('input[type="number"]');
        let matching_option = Array.from(table_e_select.options).find(opt=>parseFloat(opt.value)===parseFloat(newEValue));
        if (matching_option&&matching_option.value!=='custom') { table_e_select.value=matching_option.value; table_e_input.value=matching_option.value; table_e_input.readOnly=true; } 
        else { table_e_select.value='custom'; table_e_input.value=newEValue; table_e_input.readOnly=false; }
        
        const popupStrengthContainer = document.getElementById('popup-f-container').firstElementChild;
        const tableStrengthCell = memberRow.cells[4];
        tableStrengthCell.innerHTML = popupStrengthContainer.parentElement.innerHTML;

        memberRow.cells[5].querySelector('input').value=document.getElementById('popup-i').value;
        memberRow.cells[6].querySelector('input').value=document.getElementById('popup-a').value;
        memberRow.cells[7].querySelector('input').value=document.getElementById('popup-z').value;
        memberRow.cells[9].querySelector('select').value=document.getElementById('popup-i-conn').value;
        memberRow.cells[10].querySelector('select').value=document.getElementById('popup-j-conn').value;
        const wValue = parseFloat(document.getElementById('popup-w').value)||0;
        const memberLoadRow = Array.from(elements.memberLoadsTable.rows).find(row => parseInt(row.cells[0].querySelector('input').value)-1 === selectedMemberIndex);
        if (wValue !== 0) { if (memberLoadRow) { memberLoadRow.cells[1].querySelector('input').value=wValue; } else { addRow(elements.memberLoadsTable, [`<input type="number" value="${selectedMemberIndex+1}">`, `<input type="number" value="${wValue}">`]); } } 
        else if (memberLoadRow) { memberLoadRow.querySelector('.delete-row-btn').click(); }
        elements.memberPropsPopup.style.display='none'; runFullAnalysis(); drawOnCanvas();
    };
    document.getElementById('popup-cancel').onclick = () => { elements.memberPropsPopup.style.display = 'none'; };
    document.getElementById('popup-delete-member').onclick = () => { if(selectedMemberIndex !== null) { elements.membersTable.rows[selectedMemberIndex].querySelector('.delete-row-btn').click(); elements.memberPropsPopup.style.display='none'; } };
    document.getElementById('popup-node-load-save').onclick = () => {
        pushState();
        const px = document.getElementById('popup-px').value||0, py=document.getElementById('popup-py').value||0, mz=document.getElementById('popup-mz').value||0;
        const currentLoads = Array.from(elements.nodeLoadsTable.rows).find(row => parseInt(row.cells[0].querySelector('input').value)-1 === selectedNodeIndex);
        if (parseFloat(px)===0 && parseFloat(py)===0 && parseFloat(mz)===0) { if (currentLoads) currentLoads.querySelector('.delete-row-btn').click(); } 
        else { if (currentLoads) { currentLoads.cells[1].querySelector('input').value=px; currentLoads.cells[2].querySelector('input').value=py; currentLoads.cells[3].querySelector('input').value=mz; } 
        else { addRow(elements.nodeLoadsTable, [`<input type="number" value="${selectedNodeIndex+1}">`,`<input type="number" value="${px}">`,`<input type="number" value="${py}">`,`<input type="number" value="${mz}">`]); } }
        elements.nodeLoadPopup.style.display='none'; runFullAnalysis(); drawOnCanvas();
    };
    document.getElementById('popup-node-load-cancel').onclick = () => { elements.nodeLoadPopup.style.display = 'none'; };
    document.getElementById('popup-coords-save').onclick = () => { if(selectedNodeIndex===null)return; pushState(); const nodeRow=elements.nodesTable.rows[selectedNodeIndex]; nodeRow.cells[1].querySelector('input').value=document.getElementById('popup-x').value; nodeRow.cells[2].querySelector('input').value=document.getElementById('popup-y').value; elements.nodeCoordsPopup.style.display='none'; runFullAnalysis(); drawOnCanvas(); };
    document.getElementById('popup-coords-cancel').onclick = () => { elements.nodeCoordsPopup.style.display = 'none'; };

    document.getElementById('help-select').onclick = () => alert('【選択/移動モード】\n・節点をクリック＆ドラッグして移動します。\n・節点、部材、荷重を右クリックすると、編集メニューが表示されます。');
    document.getElementById('help-add-node').onclick = () => alert('【節点追加モード】\n・キャンバス上の好きな位置をクリックすると、新しい節点が追加されます。\n・グリッド表示時、交点近くをクリックすると自動で交点上に配置されます。\n・既存の部材上をクリックすると、その部材を2つに分割する形で節点が追加されます。');
    document.getElementById('help-add-member').onclick = () => alert('【部材追加モード】\n始点となる節点をクリックし、次に終点となる節点をクリックすると、2つの節点を結ぶ部材が追加されます。');

// --- Table Row Templates & Presets ---
const createEInputHTML = (idPrefix, currentE = '205000') => {

        const materials = { "205000": "スチール", "193000": "ステンレス", "70000": "アルミニウム", "7500": "木材(杉)", "9000": "木材(檜)", "10000": "木材(松)" };
        const e_val_str = parseFloat(currentE).toString();
        let isPresetMaterial = materials.hasOwnProperty(e_val_str);
        let options_html = '';
        for (const [value, name] of Object.entries(materials)) { options_html += `<option value="${value}" ${e_val_str === value ? 'selected' : ''}>${name}</option>`; }
        options_html += `<option value="custom" ${!isPresetMaterial ? 'selected' : ''}>任意入力</option>`;
        const selectId = `${idPrefix}-select`, inputId = `${idPrefix}-input`;
        return ` <div style="display: flex; flex-direction: column; gap: 2px;"> <select id="${selectId}" onchange="const input = document.getElementById('${inputId}'); if (this.value !== 'custom') { input.value = this.value; } input.readOnly = (this.value !== 'custom'); input.dispatchEvent(new Event('change'));"> ${options_html} </select> <input id="${inputId}" type="number" value="${currentE}" title="弾性係数 E (N/mm²)" style="display: inline-block;" ${!isPresetMaterial ? '' : 'readonly'}> </div> `;
    };
   
    const createStrengthInputHTML = (materialType, idPrefix, currentValue) => {
        let html = '';
        const selectId = `${idPrefix}-select`;
        const inputId = `${idPrefix}-input`;

        switch(materialType) {
            case 'steel': {
                const materials = { "235": "SS400, SN400B", "295": "SM490", "325": "SN490B", "355": "SM520" };
                const f_val_str = currentValue || '235';
                let isPreset = materials.hasOwnProperty(f_val_str);
                let options_html = '';
                for (const [value, name] of Object.entries(materials)) { options_html += `<option value="${value}" ${f_val_str === value ? 'selected' : ''}>${name} (F=${value})</option>`; }
                options_html += `<option value="custom" ${!isPreset ? 'selected' : ''}>任意入力</option>`;
                html = `<div data-strength-type="F-value"><select id="${selectId}" onchange="const input = document.getElementById('${inputId}'); input.value = this.value; input.readOnly = (this.value !== 'custom');">${options_html}</select><input id="${inputId}" type="number" value="${f_val_str}" ${!isPreset ? '' : 'readonly'}></div>`;
                break;
            }
            case 'wood': {
                const wood_val = currentValue || "Sugi";
                let isPresetWood = woodAllowableStresses.hasOwnProperty(wood_val);
                let html_temp = `<div data-strength-type="wood-type"><select id="${selectId}" onchange="
                    const input = document.getElementById('${inputId}');
                    if (this.value !== 'custom') {
                        input.value = woodAllowableStresses[this.value].fc[1];
                        input.readOnly = true;
                    } else {
                        input.readOnly = false;
                    }">`;
                for (const [key, value] of Object.entries(woodAllowableStresses)) { 
                    html_temp += `<option value="${key}" ${wood_val === key ? 'selected' : ''}>${value.name}</option>`; 
                }
                html_temp += `<option value="custom" ${!isPresetWood ? 'selected' : ''}>任意入力</option>`;
                const displayValue = isPresetWood ? woodAllowableStresses[wood_val].fc[1] : wood_val;
                html_temp += `</select><input id="${inputId}" type="number" value="${displayValue}" ${isPresetWood ? 'readonly' : ''}></div>`;
                html = html_temp;
                break;
            }
            case 'stainless': {
                const stainValue = currentValue || '205';
                const isPreset = ['205', '235'].includes(stainValue);
                html = `<div data-strength-type="F-stainless"><select id="${selectId}" onchange="const input = document.getElementById('${inputId}'); input.value = this.value; input.readOnly = (this.value !== 'custom');"><option value="205" ${stainValue === '205' ? 'selected' : ''}>SUS304</option><option value="235" ${stainValue === '235' ? 'selected' : ''}>SUS316</option><option value="custom" ${!isPreset ? 'selected' : ''}>任意入力</option></select><input id="${inputId}" type="number" value="${stainValue}" ${isPreset ? 'readonly' : ''}></div>`;
                break;
            }
            case 'aluminum': {
                const alumValue = currentValue || '150';
                const isPreset = ['150', '185'].includes(alumValue);
                html = `<div data-strength-type="F-aluminum"><select id="${selectId}" onchange="const input = document.getElementById('${inputId}'); input.value = this.value; input.readOnly = (this.value !== 'custom');"><option value="150" ${alumValue === '150' ? 'selected' : ''}>A5052</option><option value="185" ${alumValue === '185' ? 'selected' : ''}>A6061-T6</option><option value="custom" ${!isPreset ? 'selected' : ''}>任意入力</option></select><input id="${inputId}" type="number" value="${alumValue}" ${isPreset ? 'readonly' : ''}></div>`;
                break;
            }
            default: 
                html = '<div>-</div>';
        }
        return html;
    };


    const memberRowHTML = (i, j, E = '205000', F='235', I = 1.84e-5, A = 2.34e-3, Z = 1.23e-3, i_conn = 'rigid', j_conn = 'rigid') => {
        return [
            `<input type="number" value="${i}">`,
            `<input type="number" value="${j}">`,
            createEInputHTML(`member-e-${i}-${j}`, E),
            createStrengthInputHTML('steel', `member-strength-${i}-${j}`, F),
            `<input type="number" value="${(I * 1e8).toFixed(2)}" title="断面二次モーメント I (cm⁴)">`,
            `<input type="number" value="${(A * 1e4).toFixed(2)}" title="断面積 A (cm²)">`,
            `<input type="number" value="${(Z * 1e6).toFixed(2)}" title="断面係数 Z (cm³)">`,
            `<select><option value="rigid" ${i_conn === 'rigid' ? 'selected' : ''}>剛</option><option value="pinned" ${i_conn === 'pinned' || i_conn === 'p' ? 'selected' : ''}>ピン</option></select>`,
            `<select><option value="rigid" ${j_conn === 'rigid' ? 'selected' : ''}>剛</option><option value="pinned" ${j_conn === 'pinned' || j_conn === 'p' ? 'selected' : ''}>ピン</option></select>`
        ];
    };
    
const p_truss = {
    ic: 'p',
    jc: 'p',
    E: UNIT_CONVERSION.E_STEEL,
    I: 1e-7, // 表示時に0にならないダミー値
    Z: 1e-6, // 表示時に0にならないダミー値
};

const presets = [
    { name: '--- 1. 基本モデル (Basic Models) ---', disabled: true },
    // 1A-1: 単純梁(中央集中荷重) / Zreq≈425cm³ -> H-300x150x6.5x9 (Zx=481cm³) を選択
    { name: '1A-1: 単純梁 (中央集中荷重)', data: { nodes: [{x:0,y:0,s:'p'},{x:8,y:0,s:'r'},{x:4,y:0,s:'f'}], members: [{i:1,j:3, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:3,j:2, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4}], nl: [{n:3, py:-50}], ml: []} },
    // 1A-2: 単純梁(等分布荷重) / Zreq≈531cm³ -> H-346x174x6x9 (Zx=638cm³) を選択
    { name: '1A-2: 単純梁 (等分布荷重)', data: { nodes: [{x:0,y:0,s:'p'},{x:10,y:0,s:'r'}], members: [{i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4}], nl: [], ml: [{m:1,w:10}]} },
    // 1A-3: 片持ち梁(先端集中荷重) / Zreq≈510cm³ -> H-346x174x6x9 (Zx=638cm³) を選択
    { name: '1A-3: 片持ち梁 (先端集中荷重)', data: { nodes: [{x:0,y:0,s:'x'},{x:6,y:0,s:'f'}], members: [{i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4}], nl: [{n:2,py:-20}], ml: []} },
    // 1A-4: 片持ち梁(等分布荷重) / Zreq≈425cm³ -> H-300x150x6.5x9 (Zx=481cm³) を選択
    { name: '1A-4: 片持ち梁 (等分布荷重)', data: { nodes: [{x:0,y:0,s:'x'},{x:5,y:0,s:'f'}], members: [{i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4}], nl: [], ml: [{m:1,w:8}]} },
    // 1A-5: 両端固定梁(等分布荷重) / Zreq≈510cm³ -> H-346x174x6x9 (Zx=638cm³) を選択
    { name: '1A-5: 両端固定梁 (等分布荷重)', data: { nodes: [{x:0,y:0,s:'x'},{x:12,y:0,s:'x'}], members: [{i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4}], nl:[], ml:[{m:1,w:10}]} },
    // 1A-6: 持ち出し梁 / Zreq≈191cm³ -> H-200x100x5.5x8 (Zx=181cm³) を選択
    { name: '1A-6: 持ち出し梁', data: { nodes: [{x:0,y:0,s:'p'},{x:6,y:0,s:'r'},{x:9,y:0,s:'f'}], members: [{i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:2,j:3, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4}], nl: [{n:3,py:-15}], ml: []} },
    // 1A-7: 2径間連続梁 / Zreq≈340cm³ -> H-300x150x6.5x9 (Zx=481cm³) を選択
    { name: '1A-7: 2径間連続梁', data: { nodes: [{x:0,y:0,s:'p'},{x:8,y:0,s:'r'},{x:16,y:0,s:'r'}], members:[{i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:2,j:3, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4}], nl:[], ml:[{m:1,w:10},{m:2,w:10}]} },
    // 1A-8: L形ラーメン / Zreq≈255cm³ -> H-250x125x6x9 (Zx=317cm³) を選択
    { name: '1A-8: L形ラーメン (複合荷重)', data: { nodes: [{x:0,y:0,s:'x'},{x:0,y:4,s:'f'},{x:6,y:4,s:'f'}], members:[{i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:2,j:3, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4}], nl:[{n:3, py:-20},{n:2, px:15}], ml:[] } },
    // 1A-9: 門形ラーメン / Zreq≈255cm³ -> H-250x125x6x9 (Zx=317cm³) を選択
    { name: '1A-9: 門形ラーメン (水平荷重)', data: { nodes: [{x:0, y:0, s:'x'},{x:0, y:4, s:'f'},{x:6, y:4, s:'f'},{x:6, y:0, s:'x'}], members: [{i:1, j:2, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:2, j:3, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:3, j:4, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4}], nl: [{n:2, px:30}], ml: [] } },
    { name: '--- 2. 建築・トラス構造 (Buildings & Trusses) ---', disabled: true },
    // 2A-1: 2層ラーメン / 梁:H-200x100 (Zx=181), 柱:H-250x125 (Zx=317) を選択
    { name: '2A-1: 2層ラーメン', data: { nodes: [{x:0,y:0,s:'x'},{x:6,y:0,s:'x'},{x:12,y:0,s:'x'},{x:0,y:3.5,s:'f'},{x:6,y:3.5,s:'f'},{x:12,y:3.5,s:'f'},{x:0,y:7,s:'f'},{x:6,y:7,s:'f'},{x:12,y:7,s:'f'}], members: [
        {i:1,j:4, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:2,j:5, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:3,j:6, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:4,j:7, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:5,j:8, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:6,j:9, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},
        {i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:8,j:9, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4}
    ], nl:[], ml:[{m:7,w:15},{m:8,w:15},{m:9,w:10},{m:10,w:10}]} },
    // 2A-2, 2A-3, 2A-4, 2A-5, 2B-1, 2B-2 ... 4C-4 全てに同様の調整を実施
    { name: '2A-2: 3層ラーメン', data: { nodes: [{x:0,y:0,s:'x'},{x:6,y:0,s:'x'},{x:12,y:0,s:'x'},{x:18,y:0,s:'x'},{x:0,y:3.5,s:'f'},{x:6,y:3.5,s:'f'},{x:12,y:3.5,s:'f'},{x:18,y:3.5,s:'f'},{x:0,y:7,s:'f'},{x:6,y:7,s:'f'},{x:12,y:7,s:'f'},{x:18,y:7,s:'f'},{x:0,y:10.5,s:'f'},{x:6,y:10.5,s:'f'},{x:12,y:10.5,s:'f'},{x:18,y:10.5,s:'f'}], members: [
        {i:1,j:5, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:2,j:6, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:3,j:7, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:4,j:8, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:5,j:9, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:6,j:10, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:7,j:11, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:8,j:12, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:9,j:13, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:10,j:14, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:11,j:15, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:12,j:16, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:6,j:7, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:9,j:10, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:10,j:11, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:11,j:12, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:13,j:14, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:14,j:15, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:15,j:16, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4}
    ], nl:[], ml:[{m:13,w:15},{m:14,w:15},{m:15,w:15},{m:16,w:12},{m:17,w:12},{m:18,w:12},{m:19,w:10},{m:20,w:10},{m:21,w:10}]} },
    { name: '2A-3: 5層ラーメン', data: { nodes: [{x:0,y:0,s:'x'},{x:7,y:0,s:'x'},{x:14,y:0,s:'x'},{x:0,y:3.5,s:'f'},{x:7,y:3.5,s:'f'},{x:14,y:3.5,s:'f'},{x:0,y:7,s:'f'},{x:7,y:7,s:'f'},{x:14,y:7,s:'f'},{x:0,y:10.5,s:'f'},{x:7,y:10.5,s:'f'},{x:14,y:10.5,s:'f'},{x:0,y:14,s:'f'},{x:7,y:14,s:'f'},{x:14,y:14,s:'f'},{x:0,y:17.5,s:'f'},{x:7,y:17.5,s:'f'},{x:14,y:17.5,s:'f'}], members: [
        {i:1,j:4, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:2,j:5, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:3,j:6, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},
        {i:4,j:7, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:5,j:8, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:6,j:9, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},
        {i:7,j:10, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:8,j:11, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:9,j:12, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:10,j:13, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:11,j:14, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:12,j:15, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:13,j:16, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:14,j:17, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:15,j:18, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:8,j:9, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:10,j:11, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:11,j:12, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:13,j:14, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:14,j:15, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},
        {i:16,j:17, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:17,j:18, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4}
    ], nl:[], ml:[{m:16,w:18},{m:17,w:18},{m:18,w:15},{m:19,w:15},{m:20,w:15},{m:21,w:15},{m:22,w:12},{m:23,w:12},{m:24,w:10},{m:25,w:10}]} },
    { name: '2A-4: ブレース付3層ラーメン', data: { nodes: [{x:0,y:0,s:'x'},{x:6,y:0,s:'x'},{x:12,y:0,s:'x'},{x:0,y:3.5,s:'f'},{x:6,y:3.5,s:'f'},{x:12,y:3.5,s:'f'},{x:0,y:7,s:'f'},{x:6,y:7,s:'f'},{x:12,y:7,s:'f'},{x:0,y:10.5,s:'f'},{x:6,y:10.5,s:'f'},{x:12,y:10.5,s:'f'}], members: [
        {i:1,j:4, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:2,j:5, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:3,j:6, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:4,j:7, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:5,j:8, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:6,j:9, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:7,j:10, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:8,j:11, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:9,j:12, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},
        {i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},
        {i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:8,j:9, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},
        {i:10,j:11, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:11,j:12, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},
        {i:1,j:5, ...p_truss, A:1.269e-3},{i:2,j:4, ...p_truss, A:1.269e-3},{i:2,j:6, ...p_truss, A:1.269e-3},{i:3,j:5, ...p_truss, A:1.269e-3},
        {i:4,j:8, ...p_truss, A:1.269e-3},{i:5,j:7, ...p_truss, A:1.269e-3},{i:5,j:9, ...p_truss, A:1.269e-3},{i:6,j:8, ...p_truss, A:1.269e-3}
    ], nl:[{n:4,px:15},{n:5,px:15},{n:6,px:15},{n:7,px:12},{n:8,px:12},{n:9,px:12},{n:10,px:8},{n:11,px:8},{n:12,px:8}], ml:[{m:10,w:15},{m:11,w:15},{m:12,w:12},{m:13,w:12},{m:14,w:10},{m:15,w:10}]} },
    { name: '2A-5: 地震力の作用する3層ラーメン', data: { nodes: [{x:0,y:0,s:'x'},{x:8,y:0,s:'x'},{x:16,y:0,s:'x'},{x:0,y:4,s:'f'},{x:8,y:4,s:'f'},{x:16,y:4,s:'f'},{x:0,y:8,s:'f'},{x:8,y:8,s:'f'},{x:16,y:8,s:'f'},{x:0,y:12,s:'f'},{x:8,y:12,s:'f'},{x:16,y:12,s:'f'}], members: [
        {i:1,j:4, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:2,j:5, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:3,j:6, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:4,j:7, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:5,j:8, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:6,j:9, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:7,j:10, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:8,j:11, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:9,j:12, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:8,j:9, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:10,j:11, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:11,j:12, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4}
    ], nl:[{n:4,px:25},{n:5,px:25},{n:6,px:25},{n:7,px:20},{n:8,px:20},{n:9,px:20},{n:10,px:15},{n:11,px:15},{n:12,px:15}], ml:[{m:10,w:20},{m:11,w:20},{m:12,w:15},{m:13,w:15},{m:14,w:12},{m:15,w:12}]} },
    { name: '2B-1: 建築ラーメン (2層2スパン)', data: { nodes: [{x:0,y:0,s:'x'},{x:6,y:0,s:'x'},{x:12,y:0,s:'x'},{x:0,y:4,s:'f'},{x:6,y:4,s:'f'},{x:12,y:4,s:'f'},{x:0,y:8,s:'f'},{x:6,y:8,s:'f'},{x:12,y:8,s:'f'}], members:[
        {i:1,j:4, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:2,j:5, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:3,j:6, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:4,j:7, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:5,j:8, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:6,j:9, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:8,j:9, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4}
    ], nl:[{n:4,py:-15},{n:5,py:-15},{n:6,py:-15},{n:7,py:-15},{n:8,py:-15},{n:9,py:-15}], ml:[] } },
    { name: '2B-2: 建築ラーメン (2層2スパン・ブレース付き)', data: { nodes: [{x:0,y:0,s:'x'},{x:6,y:0,s:'x'},{x:12,y:0,s:'x'},{x:0,y:4,s:'f'},{x:6,y:4,s:'f'},{x:12,y:4,s:'f'},{x:0,y:8,s:'f'},{x:6,y:8,s:'f'},{x:12,y:8,s:'f'}], members:[
        {i:1,j:4, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:2,j:5, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:3,j:6, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},
        {i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},
        {i:4,j:7, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:5,j:8, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:6,j:9, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},
        {i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:8,j:9, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},
        {i:1,j:5, ...p_truss, A:1.269e-3},{i:5,j:9, ...p_truss, A:1.269e-3}
    ], nl:[{n:4,py:-15},{n:5,py:-15},{n:6,py:-15},{n:7,py:-15},{n:8,py:-15},{n:9,py:-15}], ml:[] } },
    { name: '2C-1: トラス屋根', data: { nodes: [{x:0,y:0,s:'p'},{x:6,y:0,s:'r'},{x:12,y:0,s:'r'},{x:3,y:2,s:'f'},{x:9,y:2,s:'f'},{x:6,y:4,s:'f'}], members:[
        {i:1,j:4, ...p_truss, A:1.269e-3},{i:4,j:6, ...p_truss, A:1.269e-3},{i:6,j:5, ...p_truss, A:1.269e-3},{i:5,j:3, ...p_truss, A:1.269e-3},
        {i:1,j:2, ...p_truss, A:1.269e-3},{i:2,j:3, ...p_truss, A:1.269e-3},{i:4,j:2, ...p_truss, A:1.269e-3},{i:2,j:5, ...p_truss, A:1.269e-3}
    ], nl:[{n:4,py:-10},{n:5,py:-10},{n:6,py:-10}], ml:[] } },
    { name: '2C-2: 平行弦トラス', data: { nodes: [{x:0,y:0,s:'p'},{x:4,y:0,s:'f'},{x:8,y:0,s:'f'},{x:12,y:0,s:'r'},{x:0,y:2,s:'f'},{x:4,y:2,s:'f'},{x:8,y:2,s:'f'},{x:12,y:2,s:'f'}], members:[
        {i:1,j:2, ...p_truss, A:1.7e-3},{i:2,j:3, ...p_truss, A:1.7e-3},{i:3,j:4, ...p_truss, A:1.7e-3},{i:5,j:6, ...p_truss, A:1.7e-3},{i:6,j:7, ...p_truss, A:1.7e-3},
        {i:7,j:8, ...p_truss, A:1.7e-3},{i:1,j:5, ...p_truss, A:1.7e-3},{i:2,j:6, ...p_truss, A:1.7e-3},{i:3,j:7, ...p_truss, A:1.7e-3},{i:4,j:8, ...p_truss, A:1.7e-3},
        {i:1,j:6, ...p_truss, A:1.7e-3},{i:2,j:7, ...p_truss, A:1.7e-3},{i:3,j:8, ...p_truss, A:1.7e-3}
    ], nl:[{n:5,py:-10},{n:6,py:-10},{n:7,py:-10},{n:8,py:-10}], ml:[] } },
    { name: '2C-3: プラット・トラス', data: { nodes: [{x:0,y:0,s:'p'},{x:3,y:0,s:'f'},{x:6,y:0,s:'f'},{x:9,y:0,s:'f'},{x:12,y:0,s:'r'},{x:0,y:2,s:'f'},{x:3,y:2,s:'f'},{x:6,y:2,s:'f'},{x:9,y:2,s:'f'},{x:12,y:2,s:'f'}], members:[
        {i:1,j:2, ...p_truss, A:1.7e-3},{i:2,j:3, ...p_truss, A:1.7e-3},{i:3,j:4, ...p_truss, A:1.7e-3},{i:4,j:5, ...p_truss, A:1.7e-3},
        {i:6,j:7, ...p_truss, A:1.7e-3},{i:7,j:8, ...p_truss, A:1.7e-3},{i:8,j:9, ...p_truss, A:1.7e-3},{i:9,j:10, ...p_truss, A:1.7e-3},
        {i:1,j:6, ...p_truss, A:1.269e-3},{i:2,j:7, ...p_truss, A:1.269e-3},{i:3,j:8, ...p_truss, A:1.269e-3},{i:4,j:9, ...p_truss, A:1.269e-3},{i:5,j:10, ...p_truss, A:1.269e-3},
        {i:1,j:7, ...p_truss, A:1.269e-3},{i:2,j:8, ...p_truss, A:1.269e-3},{i:3,j:9, ...p_truss, A:1.269e-3},{i:4,j:10, ...p_truss, A:1.269e-3}
    ], nl:[{n:6,py:-10},{n:7,py:-10},{n:8,py:-10},{n:9,py:-10},{n:10,py:-10}], ml:[] } },
    { name: '2C-4: ハウ・トラス', data: { nodes: [{x:0,y:0,s:'p'},{x:3,y:0,s:'f'},{x:6,y:0,s:'f'},{x:9,y:0,s:'f'},{x:12,y:0,s:'r'},{x:0,y:2,s:'f'},{x:3,y:2,s:'f'},{x:6,y:2,s:'f'},{x:9,y:2,s:'f'},{x:12,y:2,s:'f'}], members:[
        {i:1,j:2, ...p_truss, A:1.7e-3},{i:2,j:3, ...p_truss, A:1.7e-3},{i:3,j:4, ...p_truss, A:1.7e-3},{i:4,j:5, ...p_truss, A:1.7e-3},
        {i:6,j:7, ...p_truss, A:1.7e-3},{i:7,j:8, ...p_truss, A:1.7e-3},{i:8,j:9, ...p_truss, A:1.7e-3},{i:9,j:10, ...p_truss, A:1.7e-3},
        {i:1,j:6, ...p_truss, A:1.269e-3},{i:2,j:7, ...p_truss, A:1.269e-3},{i:3,j:8, ...p_truss, A:1.269e-3},{i:4,j:9, ...p_truss, A:1.269e-3},{i:5,j:10, ...p_truss, A:1.269e-3},
        {i:6,j:2, ...p_truss, A:1.269e-3},{i:7,j:3, ...p_truss, A:1.269e-3},{i:8,j:4, ...p_truss, A:1.269e-3},{i:9,j:5, ...p_truss, A:1.269e-3}
    ], nl:[{n:6,py:-10},{n:7,py:-10},{n:8,py:-10},{n:9,py:-10},{n:10,py:-10}], ml:[] } },
    { name: '2C-5: ワーレン・トラス', data: { nodes: [{x:0,y:0,s:'p'},{x:6,y:0,s:'r'},{x:12,y:0,s:'f'},{x:3,y:2,s:'f'},{x:9,y:2,s:'f'}], members:[
        {i:1,j:4, ...p_truss, A:1.7e-3},{i:4,j:2, ...p_truss, A:1.7e-3},{i:2,j:5, ...p_truss, A:1.7e-3},{i:5,j:3, ...p_truss, A:1.7e-3},
        {i:4,j:5, ...p_truss, A:1.7e-3},{i:1,j:2, ...p_truss, A:1.7e-3},{i:2,j:3, ...p_truss, A:1.7e-3}
    ], nl:[{n:4,py:-15},{n:5,py:-15}], ml:[] } },
    { name: '--- 3. 橋梁構造物 (Bridge Structures) ---', disabled: true },
    { name: '3A-1: 単純支持桁橋', data: { nodes: [{x:0,y:0,s:'p'},{x:3,y:0,s:'f'},{x:6,y:0,s:'f'},{x:9,y:0,s:'f'},{x:12,y:0,s:'r'}], members:[
        {i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:2.35e-4, A:8.337e-3, Z:1.17e-3},{i:2,j:3, E:UNIT_CONVERSION.E_STEEL, I:2.35e-4, A:8.337e-3, Z:1.17e-3},
        {i:3,j:4, E:UNIT_CONVERSION.E_STEEL, I:2.35e-4, A:8.337e-3, Z:1.17e-3},{i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:2.35e-4, A:8.337e-3, Z:1.17e-3}
    ], nl:[], ml:[{m:1,w:20},{m:2,w:20},{m:3,w:20},{m:4,w:20}] } },
    { name: '3A-2: 2径間連続桁橋', data: { nodes: [{x:0,y:0,s:'p'},{x:4,y:0,s:'f'},{x:8,y:0,s:'r'},{x:12,y:0,s:'f'},{x:16,y:0,s:'r'}], members:[
        {i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:2,j:3, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},
        {i:3,j:4, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4}
    ], nl:[], ml:[{m:1,w:20},{m:2,w:20},{m:3,w:20},{m:4,w:20}] } },
    { name: '3A-3: ゲルバー桁橋', data: { nodes: [{x:0, y:0, s:'p'},{x:4, y:0, s:'f'},{x:8, y:0, s:'r'},{x:12, y:0, s:'f'},{x:16, y:0, s:'r'}], members: [
        {i:1, j:2, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:2, j:3, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4, i_conn:'p', j_conn:'rigid'},
        {i:3, j:4, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4, i_conn:'rigid', j_conn:'p'},{i:4, j:5, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4}
    ], nl: [], ml: [{m:1, w:20},{m:2, w:20},{m:3, w:20},{m:4, w:20}] } },
    { name: '3B-1: 単純トラス橋', data: { nodes: [{x:0,y:0,s:'p'},{x:6,y:0,s:'f'},{x:12,y:0,s:'r'},{x:0,y:3,s:'f'},{x:6,y:3,s:'f'},{x:12,y:3,s:'f'}], members:[
        {i:1,j:2, ...p_truss, A:3.697e-3},{i:2,j:3, ...p_truss, A:3.697e-3},
        {i:4,j:5, ...p_truss, A:3.697e-3},{i:5,j:6, ...p_truss, A:3.697e-3},
        {i:1,j:4, ...p_truss, A:1.7e-3},{i:2,j:5, ...p_truss, A:1.7e-3},{i:3,j:6, ...p_truss, A:1.7e-3},
        {i:1,j:5, ...p_truss, A:1.7e-3},{i:2,j:6, ...p_truss, A:1.7e-3}
    ], nl:[{n:1,py:-30},{n:2,py:-30},{n:3,py:-30}], ml:[] } },
    { name: '3B-2: 2径間連続トラス橋', data: { nodes: [{x:0,y:0,s:'p'},{x:6,y:0,s:'f'},{x:12,y:0,s:'r'},{x:18,y:0,s:'f'},{x:24,y:0,s:'r'},{x:0,y:3,s:'f'},{x:6,y:3,s:'f'},{x:12,y:3,s:'f'},{x:18,y:3,s:'f'},{x:24,y:3,s:'f'}], members:[
        {i:1,j:2, ...p_truss, A:4.678e-3},{i:2,j:3, ...p_truss, A:4.678e-3},{i:3,j:4, ...p_truss, A:4.678e-3},{i:4,j:5, ...p_truss, A:4.678e-3},
        {i:6,j:7, ...p_truss, A:4.678e-3},{i:7,j:8, ...p_truss, A:4.678e-3},{i:8,j:9, ...p_truss, A:4.678e-3},{i:9,j:10, ...p_truss, A:4.678e-3},
        {i:1,j:6, ...p_truss, A:1.7e-3},{i:2,j:7, ...p_truss, A:1.7e-3},{i:3,j:8, ...p_truss, A:1.7e-3},{i:4,j:9, ...p_truss, A:1.7e-3},{i:5,j:10, ...p_truss, A:1.7e-3},
        {i:6,j:2, ...p_truss, A:1.7e-3},{i:7,j:3, ...p_truss, A:1.7e-3},{i:8,j:4, ...p_truss, A:1.7e-3},{i:9,j:5, ...p_truss, A:1.7e-3},
        {i:7,j:2, ...p_truss, A:1.7e-3},{i:8,j:3, ...p_truss, A:1.7e-3},{i:9,j:4, ...p_truss, A:1.7e-3}
    ], nl:[{n:1,py:-40},{n:2,py:-40},{n:3,py:-40},{n:4,py:-40},{n:5,py:-40}], ml:[] } },
    { name: '3B-3: ゲルバートラス橋', data: { nodes: [{x:0,y:0,s:'p'},{x:6,y:0,s:'f'},{x:12,y:0,s:'r'},{x:18,y:0,s:'f'},{x:24,y:0,s:'r'},{x:0,y:3,s:'f'},{x:6,y:3,s:'f'},{x:12,y:3,s:'f'},{x:18,y:3,s:'f'},{x:24,y:3,s:'f'},{x:9,y:0,s:'f'},{x:15,y:0,s:'f'}], members:[
        {i:1,j:2, ...p_truss, A:3.697e-3},{i:2,j:11, ...p_truss, A:3.697e-3},{i:11,j:12, ...p_truss, A:3.697e-3},{i:12,j:4, ...p_truss, A:3.697e-3},{i:4,j:5, ...p_truss, A:3.697e-3},
        {i:6,j:7, ...p_truss, A:3.697e-3},{i:7,j:8, ...p_truss, A:3.697e-3},{i:8,j:9, ...p_truss, A:3.697e-3},{i:9,j:10, ...p_truss, A:3.697e-3},
        {i:1,j:6, ...p_truss, A:1.7e-3},{i:2,j:7, ...p_truss, A:1.7e-3},{i:11,j:8, ...p_truss, A:1.7e-3},{i:12,j:8, ...p_truss, A:1.7e-3},{i:4,j:9, ...p_truss, A:1.7e-3},{i:5,j:10, ...p_truss, A:1.7e-3},
        {i:1,j:7, ...p_truss, A:1.7e-3},{i:2,j:6, ...p_truss, A:1.7e-3},{i:2,j:8, ...p_truss, A:1.7e-3},{i:4,j:8, ...p_truss, A:1.7e-3},{i:4,j:10, ...p_truss, A:1.7e-3},{i:5,j:9, ...p_truss, A:1.7e-3}
    ], nl:[{n:1,py:-40},{n:2,py:-40},{n:11,py:-40},{n:12,py:-40},{n:4,py:-40},{n:5,py:-40}], ml:[] } },
    { name: '3C-1: 2ヒンジアーチ橋', data: { nodes: [{x:0,y:0,s:'p'},{x:4,y:2,s:'f'},{x:8,y:3,s:'f'},{x:12,y:3.5,s:'f'},{x:16,y:3,s:'f'},{x:20,y:2,s:'f'},{x:24,y:0,s:'r'}], members:[
        {i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:2,j:3, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},
        {i:3,j:4, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},
        {i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:6,j:7, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4}
    ], nl:[{n:2,py:-20},{n:3,py:-20},{n:4,py:-20},{n:5,py:-20},{n:6,py:-20}], ml:[] } },
    { name: '3C-2: 3ヒンジアーチ橋', data: { nodes: [{x:0,y:0,s:'p'},{x:4,y:2,s:'f'},{x:8,y:3,s:'f'},{x:12,y:3.5,s:'f'},{x:16,y:3,s:'f'},{x:20,y:2,s:'f'},{x:24,y:0,s:'r'}], members:[
        {i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:2,j:3, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:3,j:4, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4, j_conn:'p'},
        {i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4, i_conn:'p'},{i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:6,j:7, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4}
    ], nl:[{n:2,py:-20},{n:3,py:-20},{n:4,py:-20},{n:5,py:-20},{n:6,py:-20}], ml:[] } },
    { name: '3C-3: タイドアーチ橋', data: { nodes: [{x:0,y:0,s:'p'},{x:4,y:2,s:'f'},{x:8,y:3,s:'f'},{x:12,y:3.5,s:'f'},{x:16,y:3,s:'f'},{x:20,y:2,s:'f'},{x:24,y:0,s:'r'}], members:[
        {i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:2,j:3, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:3,j:4, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},
        {i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:6,j:7, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},
        {i:1,j:7, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4}
    ], nl:[{n:2,py:-20},{n:3,py:-20},{n:4,py:-20},{n:5,py:-20},{n:6,py:-20}], ml:[] } },
    { name: '3D-1: ランガー橋', data: { nodes: [{x:0,y:0,s:'p'},{x:6,y:0,s:'f'},{x:12,y:0,s:'f'},{x:18,y:0,s:'f'},{x:24,y:0,s:'r'},{x:6,y:4,s:'f'},{x:12,y:5,s:'f'},{x:18,y:4,s:'f'}], members:[
        {i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:2,j:3, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:3,j:4, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},
        {i:1,j:6, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:6,j:7, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:8,j:5, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:2,j:6, ...p_truss, A:1.7e-3},{i:3,j:7, ...p_truss, A:1.7e-3},{i:4,j:8, ...p_truss, A:1.7e-3}
    ], nl:[{n:2,py:-20},{n:3,py:-20},{n:4,py:-20}], ml:[] } },
    { name: '3D-2: ローゼ橋', data: { nodes: [{x:0,y:0,s:'p'},{x:6,y:0,s:'f'},{x:12,y:0,s:'f'},{x:18,y:0,s:'f'},{x:24,y:0,s:'r'},{x:0,y:4,s:'f'},{x:6,y:5,s:'f'},{x:12,y:5.5,s:'f'},{x:18,y:5,s:'f'},{x:24,y:4,s:'f'}], members:[
        {i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:2,j:3, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:3,j:4, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},
        {i:6,j:7, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:8,j:9, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:9,j:10, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:1,j:6, ...p_truss, A:1.7e-3},{i:2,j:7, ...p_truss, A:1.7e-3},{i:3,j:8, ...p_truss, A:1.7e-3},{i:4,j:9, ...p_truss, A:1.7e-3},{i:5,j:10, ...p_truss, A:1.7e-3},
        {i:2,j:6, ...p_truss, A:1.7e-3},{i:3,j:7, ...p_truss, A:1.7e-3},{i:4,j:8, ...p_truss, A:1.7e-3},{i:5,j:9, ...p_truss, A:1.7e-3}
    ], nl:[{n:2,py:-20},{n:3,py:-20},{n:4,py:-20}], ml:[] } },
    { name: '3D-3: 斜張橋', data: { nodes: [{x:0,y:0,s:'p'},{x:6,y:0,s:'f'},{x:12,y:0,s:'r'},{x:18,y:0,s:'f'},{x:24,y:0,s:'r'},{x:12,y:8,s:'f'}], members:[
        {i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:2,j:3, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:3,j:4, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:3,j:6, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},
        {i:1,j:6, ...p_truss, A:2.667e-3},{i:2,j:6, ...p_truss, A:2.667e-3},{i:4,j:6, ...p_truss, A:2.667e-3},{i:5,j:6, ...p_truss, A:2.667e-3}
    ], nl:[{n:2,py:-20},{n:4,py:-20}], ml:[] } },
    { name: '--- 4. その他・特殊構造 (Misc. & Special) ---', disabled: true },
    { name: '4A-1: 高層ビル', data: { nodes: [{x:0,y:0,s:'x'},{x:8,y:0,s:'x'},{x:16,y:0,s:'x'},{x:0,y:4,s:'f'},{x:8,y:4,s:'f'},{x:16,y:4,s:'f'},{x:0,y:8,s:'f'},{x:8,y:8,s:'f'},{x:16,y:8,s:'f'},{x:0,y:12,s:'f'},{x:8,y:12,s:'f'},{x:16,y:12,s:'f'},{x:0,y:16,s:'f'},{x:8,y:16,s:'f'},{x:16,y:16,s:'f'}], members:[
        {i:1,j:4, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:2,j:5, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},{i:3,j:6, E:UNIT_CONVERSION.E_STEEL, I:1.35e-4, A:6.291e-3, Z:7.71e-4},
        {i:4,j:7, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},{i:5,j:8, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},{i:6,j:9, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},
        {i:7,j:10, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:8,j:11, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:9,j:12, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:10,j:13, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:11,j:14, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:12,j:15, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:8,j:9, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:10,j:11, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:11,j:12, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},
        {i:13,j:14, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:14,j:15, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4}
    ], nl:[{n:13,px:10},{n:14,px:10},{n:15,px:10},{n:13,py:-30},{n:14,py:-30},{n:15,py:-30}], ml:[] } },
    { name: '4A-2: 大スパン屋根', data: { nodes: [{x:0,y:0,s:'p'},{x:8,y:0,s:'r'},{x:16,y:0,s:'r'},{x:24,y:0,s:'p'},{x:4,y:7,s:'f'},{x:12,y:9,s:'f'},{x:20,y:7,s:'f'}], members:[
        {i:1,j:5, ...p_truss, A:3.697e-3},{i:5,j:2, ...p_truss, A:3.697e-3},{i:2,j:6, ...p_truss, A:3.697e-3},{i:6,j:3, ...p_truss, A:3.697e-3},
        {i:3,j:7, ...p_truss, A:3.697e-3},{i:7,j:4, ...p_truss, A:3.697e-3},{i:5,j:6, ...p_truss, A:3.697e-3},{i:6,j:7, ...p_truss, A:3.697e-3},
        {i:1,j:2, ...p_truss, A:2.667e-3},{i:2,j:3, ...p_truss, A:2.667e-3},{i:3,j:4, ...p_truss, A:2.667e-3}
    ], nl:[{n:5,py:-10},{n:6,py:-10},{n:7,py:-10}], ml:[] } },
    { name: '4A-3: 複合ラーメン構造', data: { nodes: [{x:0,y:0,s:'x'},{x:8,y:0,s:'x'},{x:16,y:0,s:'x'},{x:24,y:0,s:'x'},{x:0,y:4,s:'f'},{x:8,y:4,s:'f'},{x:16,y:4,s:'f'},{x:24,y:4,s:'f'},{x:0,y:8,s:'f'},{x:8,y:8,s:'f'},{x:16,y:8,s:'f'},{x:24,y:8,s:'f'}], members:[
        {i:1,j:5, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:2,j:6, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:3,j:7, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:4,j:8, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:5,j:9, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:6,j:10, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:7,j:11, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:8,j:12, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:6,j:7, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:9,j:10, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:10,j:11, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:11,j:12, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:1,j:6, ...p_truss, A:1.7e-3},{i:2,j:5, ...p_truss, A:1.7e-3},{i:2,j:7, ...p_truss, A:1.7e-3},{i:3,j:6, ...p_truss, A:1.7e-3},
        {i:3,j:8, ...p_truss, A:1.7e-3},{i:4,j:7, ...p_truss, A:1.7e-3},{i:5,j:10, ...p_truss, A:1.7e-3},{i:6,j:9, ...p_truss, A:1.7e-3},
        {i:6,j:11, ...p_truss, A:1.7e-3},{i:7,j:10, ...p_truss, A:1.7e-3},{i:7,j:12, ...p_truss, A:1.7e-3},{i:8,j:11, ...p_truss, A:1.7e-3}
    ], nl:[{n:9,px:20},{n:10,px:20},{n:11,px:20},{n:12,px:20},{n:9,py:-30},{n:10,py:-30},{n:11,py:-30},{n:12,py:-30}], ml:[] } },
    { name: '4B-1: 下路アーチ橋', data: { nodes: [{x:0,y:0,s:'p'},{x:6,y:0,s:'f'},{x:12,y:0,s:'f'},{x:18,y:0,s:'f'},{x:24,y:0,s:'r'},{x:6,y:4,s:'f'},{x:12,y:5,s:'f'},{x:18,y:4,s:'f'}], members:[
        {i:1,j:2, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:2,j:3, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:3,j:4, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:1,j:6, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:6,j:7, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},{i:8,j:5, E:UNIT_CONVERSION.E_STEEL, I:3.96e-5, A:3.697e-3, Z:3.17e-4},
        {i:2,j:6, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:3,j:7, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4},{i:4,j:8, E:UNIT_CONVERSION.E_STEEL, I:1.81e-5, A:2.667e-3, Z:1.81e-4}
    ], nl:[{n:2,py:-20},{n:3,py:-20},{n:4,py:-20}], ml:[] } },
    { name: '4B-2: 複合トラス橋', data: { nodes: [{x:0,y:0,s:'p'},{x:6,y:0,s:'f'},{x:12,y:0,s:'f'},{x:18,y:0,s:'f'},{x:24,y:0,s:'r'},{x:0,y:4,s:'f'},{x:6,y:4,s:'f'},{x:12,y:4,s:'f'},{x:18,y:4,s:'f'},{x:24,y:4,s:'f'},{x:6,y:8,s:'f'},{x:12,y:9,s:'f'},{x:18,y:8,s:'f'}], members:[
        {i:1,j:2, ...p_truss, A:3.697e-3},{i:2,j:3, ...p_truss, A:3.697e-3},{i:3,j:4, ...p_truss, A:3.697e-3},{i:4,j:5, ...p_truss, A:3.697e-3},
        {i:6,j:7, ...p_truss, A:3.697e-3},{i:7,j:8, ...p_truss, A:3.697e-3},{i:8,j:9, ...p_truss, A:3.697e-3},{i:9,j:10, ...p_truss, A:3.697e-3},
        {i:7,j:11, ...p_truss, A:2.667e-3},{i:8,j:12, ...p_truss, A:2.667e-3},{i:9,j:13, ...p_truss, A:2.667e-3},{i:11,j:12, ...p_truss, A:2.667e-3},{i:12,j:13, ...p_truss, A:2.667e-3},
        {i:1,j:6, ...p_truss, A:1.7e-3},{i:2,j:7, ...p_truss, A:1.7e-3},{i:3,j:8, ...p_truss, A:1.7e-3},{i:4,j:9, ...p_truss, A:1.7e-3},{i:5,j:10, ...p_truss, A:1.7e-3},
        {i:6,j:2, ...p_truss, A:1.7e-3},{i:7,j:3, ...p_truss, A:1.7e-3},{i:8,j:4, ...p_truss, A:1.7e-3},{i:9,j:5, ...p_truss, A:1.7e-3},
        {i:7,j:12, ...p_truss, A:1.7e-3},{i:8,j:11, ...p_truss, A:1.7e-3},{i:8,j:13, ...p_truss, A:1.7e-3},{i:9,j:12, ...p_truss, A:1.7e-3}
    ], nl:[{n:1,py:-20},{n:2,py:-20},{n:3,py:-20},{n:4,py:-20},{n:5,py:-20}], ml:[] } },
    { name: '4B-3: 吊床版橋', data: { nodes: [{x:0,y:0,s:'x'},{x:36,y:0,s:'x'},{x:0,y:12,s:'f'},{x:36,y:12,s:'f'},{x:6,y:0,s:'f'},{x:12,y:0,s:'f'},{x:18,y:0,s:'f'},{x:24,y:0,s:'f'},{x:30,y:0,s:'f'},{x:6,y:9,s:'f'},{x:12,y:8,s:'f'},{x:18,y:7,s:'f'},{x:24,y:8,s:'f'},{x:30,y:9,s:'f'}], members:[
        {i:1,j:3, E:UNIT_CONVERSION.E_STEEL, I:2.35e-4, A:8.337e-3, Z:1.17e-3},{i:2,j:4, E:UNIT_CONVERSION.E_STEEL, I:2.35e-4, A:8.337e-3, Z:1.17e-3},
        {i:3,j:10, ...p_truss, A:4.678e-3},{i:10,j:11, ...p_truss, A:4.678e-3},{i:11,j:12, ...p_truss, A:4.678e-3},{i:12,j:13, ...p_truss, A:4.678e-3},
        {i:13,j:14, ...p_truss, A:4.678e-3},{i:14,j:4, ...p_truss, A:4.678e-3},
        {i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:6,j:7, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:8,j:9, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:5,j:10, ...p_truss, A:1.7e-3},{i:6,j:11, ...p_truss, A:1.7e-3},{i:7,j:12, ...p_truss, A:1.7e-3},{i:8,j:13, ...p_truss, A:1.7e-3},{i:9,j:14, ...p_truss, A:1.7e-3}
    ], nl:[{n:5,py:-15},{n:6,py:-15},{n:7,py:-15},{n:8,py:-15},{n:9,py:-15}], ml:[] } },
    { name: '4B-4: 斜張橋', data: { nodes: [{x:0,y:0,s:'p'},{x:50,y:0,s:'r'},{x:25,y:0,s:'r'},{x:25,y:20,s:'f'},{x:10,y:0,s:'f'},{x:20,y:0,s:'f'},{x:30,y:0,s:'f'},{x:40,y:0,s:'f'}], members:[
        {i:3,j:4, E:UNIT_CONVERSION.E_STEEL, I:2.35e-4, A:8.337e-3, Z:1.17e-3},
        {i:4,j:5, ...p_truss, A:3.697e-3},{i:4,j:6, ...p_truss, A:3.697e-3},{i:4,j:7, ...p_truss, A:3.697e-3},{i:4,j:8, ...p_truss, A:3.697e-3},
        {i:1,j:5, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:6,j:3, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:3,j:7, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:8,j:2, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4}
    ], nl:[{n:5,py:-20},{n:6,py:-20},{n:7,py:-20},{n:8,py:-20}], ml:[] } },
    { name: '4B-5: 複合アーチ橋', data: { nodes: [{x:0,y:0,s:'x'},{x:40,y:0,s:'p'},{x:8,y:0,s:'f'},{x:16,y:0,s:'f'},{x:24,y:0,s:'f'},{x:32,y:0,s:'f'},{x:8,y:6,s:'f'},{x:16,y:8,s:'f'},{x:24,y:8,s:'f'},{x:32,y:6,s:'f'},{x:20,y:10,s:'f'}], members:[
        {i:1,j:3, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:3,j:4, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},{i:6,j:2, E:UNIT_CONVERSION.E_STEEL, I:7.21e-5, A:4.678e-3, Z:4.81e-4},
        {i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},{i:8,j:11, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},
        {i:11,j:9, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},{i:9,j:10, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},
        {i:3,j:7, ...p_truss, A:1.7e-3},{i:4,j:8, ...p_truss, A:1.7e-3},{i:5,j:9, ...p_truss, A:1.7e-3},{i:6,j:10, ...p_truss, A:1.7e-3},
        {i:3,j:8, ...p_truss, A:1.7e-3},{i:4,j:7, ...p_truss, A:1.7e-3},{i:4,j:9, ...p_truss, A:1.7e-3},{i:5,j:8, ...p_truss, A:1.7e-3},
        {i:5,j:10, ...p_truss, A:1.7e-3},{i:6,j:9, ...p_truss, A:1.7e-3}
    ], nl:[{n:3,py:-15},{n:4,py:-15},{n:5,py:-15},{n:6,py:-15}], ml:[] } },
    { name: '4C-1: 高層建物＋制振装置', data: { nodes: [{x:0,y:0,s:'x'},{x:8,y:0,s:'x'},{x:16,y:0,s:'x'},{x:0,y:4,s:'f'},{x:8,y:4,s:'f'},{x:16,y:4,s:'f'},{x:0,y:8,s:'f'},{x:8,y:8,s:'f'},{x:16,y:8,s:'f'},{x:0,y:12,s:'f'},{x:8,y:12,s:'f'},{x:16,y:12,s:'f'},{x:0,y:16,s:'f'},{x:8,y:16,s:'f'},{x:16,y:16,s:'f'},{x:0,y:20,s:'f'},{x:8,y:20,s:'f'},{x:16,y:20,s:'f'},{x:0,y:24,s:'f'},{x:8,y:24,s:'f'},{x:16,y:24,s:'f'},{x:0,y:28,s:'f'},{x:8,y:28,s:'f'},{x:16,y:28,s:'f'},{x:0,y:32,s:'f'},{x:8,y:32,s:'f'},{x:16,y:32,s:'f'},{x:0,y:36,s:'f'},{x:8,y:36,s:'f'},{x:16,y:36,s:'f'}], members:[
        {i:1,j:4,E:205000,I:6.66e-4,A:2.187e-2,Z:3.33e-3},{i:4,j:7,E:205000,I:6.66e-4,A:2.187e-2,Z:3.33e-3},{i:7,j:10,E:205000,I:5.61e-4,A:1.868e-2,Z:2.85e-3},{i:10,j:13,E:205000,I:5.61e-4,A:1.868e-2,Z:2.85e-3},{i:13,j:16,E:205000,I:3.98e-4,A:1.719e-2,Z:2.28e-3},{i:16,j:19,E:205000,I:3.98e-4,A:1.719e-2,Z:2.28e-3},{i:19,j:22,E:205000,I:2.35e-4,A:8.337e-3,Z:1.17e-3},{i:22,j:25,E:205000,I:2.35e-4,A:8.337e-3,Z:1.17e-3},{i:25,j:28,E:205000,I:1.35e-4,A:6.291e-3,Z:7.71e-4},
        {i:2,j:5,E:205000,I:6.66e-4,A:2.187e-2,Z:3.33e-3},{i:5,j:8,E:205000,I:6.66e-4,A:2.187e-2,Z:3.33e-3},{i:8,j:11,E:205000,I:5.61e-4,A:1.868e-2,Z:2.85e-3},{i:11,j:14,E:205000,I:5.61e-4,A:1.868e-2,Z:2.85e-3},{i:14,j:17,E:205000,I:3.98e-4,A:1.719e-2,Z:2.28e-3},{i:17,j:20,E:205000,I:3.98e-4,A:1.719e-2,Z:2.28e-3},{i:20,j:23,E:205000,I:2.35e-4,A:8.337e-3,Z:1.17e-3},{i:23,j:26,E:205000,I:2.35e-4,A:8.337e-3,Z:1.17e-3},{i:26,j:29,E:205000,I:1.35e-4,A:6.291e-3,Z:7.71e-4},
        {i:3,j:6,E:205000,I:6.66e-4,A:2.187e-2,Z:3.33e-3},{i:6,j:9,E:205000,I:6.66e-4,A:2.187e-2,Z:3.33e-3},{i:9,j:12,E:205000,I:5.61e-4,A:1.868e-2,Z:2.85e-3},{i:12,j:15,E:205000,I:5.61e-4,A:1.868e-2,Z:2.85e-3},{i:15,j:18,E:205000,I:3.98e-4,A:1.719e-2,Z:2.28e-3},{i:18,j:21,E:205000,I:3.98e-4,A:1.719e-2,Z:2.28e-3},{i:21,j:24,E:205000,I:2.35e-4,A:8.337e-3,Z:1.17e-3},{i:24,j:27,E:205000,I:2.35e-4,A:8.337e-3,Z:1.17e-3},{i:27,j:30,E:205000,I:1.35e-4,A:6.291e-3,Z:7.71e-4},
        {i:4,j:5,E:205000,I:2.35e-4,A:8.337e-3,Z:1.17e-3},{i:5,j:6,E:205000,I:2.35e-4,A:8.337e-3,Z:1.17e-3},{i:7,j:8,E:205000,I:2.35e-4,A:8.337e-3,Z:1.17e-3},{i:8,j:9,E:205000,I:2.35e-4,A:8.337e-3,Z:1.17e-3},{i:10,j:11,E:205000,I:1.35e-4,A:6.291e-3,Z:7.71e-4},{i:11,j:12,E:205000,I:1.35e-4,A:6.291e-3,Z:7.71e-4},{i:13,j:14,E:205000,I:1.35e-4,A:6.291e-3,Z:7.71e-4},{i:14,j:15,E:205000,I:1.35e-4,A:6.291e-3,Z:7.71e-4},{i:16,j:17,E:205000,I:1.35e-4,A:6.291e-3,Z:7.71e-4},{i:17,j:18,E:205000,I:1.35e-4,A:6.291e-3,Z:7.71e-4},{i:19,j:20,E:205000,I:7.21e-5,A:4.678e-3,Z:4.81e-4},{i:20,j:21,E:205000,I:7.21e-5,A:4.678e-3,Z:4.81e-4},{i:22,j:23,E:205000,I:7.21e-5,A:4.678e-3,Z:4.81e-4},{i:23,j:24,E:205000,I:7.21e-5,A:4.678e-3,Z:4.81e-4},{i:25,j:26,E:205000,I:7.21e-5,A:4.678e-3,Z:4.81e-4},{i:26,j:27,E:205000,I:7.21e-5,A:4.678e-3,Z:4.81e-4},{i:28,j:29,E:205000,I:7.21e-5,A:4.678e-3,Z:4.81e-4},{i:29,j:30,E:205000,I:7.21e-5,A:4.678e-3,Z:4.81e-4},
        {i:4,j:8, ...p_truss, A:1.269e-3},{i:5,j:9, ...p_truss, A:1.269e-3},{i:7,j:11, ...p_truss, A:1.269e-3},{i:8,j:12, ...p_truss, A:1.269e-3},
        {i:13,j:17, ...p_truss, A:1.269e-3},{i:14,j:18, ...p_truss, A:1.269e-3},{i:16,j:20, ...p_truss, A:1.269e-3},{i:17,j:21, ...p_truss, A:1.269e-3},
        {i:22,j:26, ...p_truss, A:1.269e-3},{i:23,j:27, ...p_truss, A:1.269e-3},{i:25,j:29, ...p_truss, A:1.269e-3},{i:26,j:30, ...p_truss, A:1.269e-3}
    ], nl:[{n:4,px:10},{n:7,px:10},{n:10,px:10},{n:13,px:10},{n:16,px:10},{n:19,px:10},{n:22,px:10},{n:25,px:10},{n:28,px:10}], ml:[] } },
    { name: '4C-2: 大スパン立体トラス', data: { nodes: [{x:0, y:0, s:'p'},{x:6, y:0, s:'f'},{x:12, y:0, s:'f'},{x:18, y:0, s:'f'},{x:24, y:0, s:'f'},{x:30, y:0, s:'f'},{x:36, y:0, s:'r'},{x:0, y:6, s:'f'},{x:6, y:6, s:'f'},{x:12, y:6, s:'f'},{x:18, y:6, s:'f'},{x:24, y:6, s:'f'},{x:30, y:6, s:'f'},{x:36, y:6, s:'f'}], members:[
        {i:1,j:2, ...p_truss, A:2.667e-3},{i:2,j:3, ...p_truss, A:2.667e-3},{i:3,j:4, ...p_truss, A:2.667e-3},{i:4,j:5, ...p_truss, A:2.667e-3},{i:5,j:6, ...p_truss, A:2.667e-3},{i:6,j:7, ...p_truss, A:2.667e-3},
        {i:8,j:9, ...p_truss, A:2.667e-3},{i:9,j:10, ...p_truss, A:2.667e-3},{i:10,j:11, ...p_truss, A:2.667e-3},{i:11,j:12, ...p_truss, A:2.667e-3},{i:12,j:13, ...p_truss, A:2.667e-3},{i:13,j:14, ...p_truss, A:2.667e-3},
        {i:1,j:8, ...p_truss, A:1.7e-3},{i:2,j:9, ...p_truss, A:1.7e-3},{i:3,j:10, ...p_truss, A:1.7e-3},{i:4,j:11, ...p_truss, A:1.7e-3},{i:5,j:12, ...p_truss, A:1.7e-3},{i:6,j:13, ...p_truss, A:1.7e-3},{i:7,j:14, ...p_truss, A:1.7e-3},
        {i:1,j:9, ...p_truss, A:1.7e-3},{i:2,j:10, ...p_truss, A:1.7e-3},{i:3,j:11, ...p_truss, A:1.7e-3},{i:4,j:12, ...p_truss, A:1.7e-3},{i:5,j:13, ...p_truss, A:1.7e-3},{i:6,j:14, ...p_truss, A:1.7e-3},
        {i:8,j:2, ...p_truss, A:1.7e-3},{i:9,j:3, ...p_truss, A:1.7e-3},{i:10,j:4, ...p_truss, A:1.7e-3},{i:11,j:5, ...p_truss, A:1.7e-3},{i:12,j:6, ...p_truss, A:1.7e-3},{i:13,j:7, ...p_truss, A:1.7e-3}
    ], nl:[{n:8,py:-15},{n:9,py:-15},{n:10,py:-15},{n:11,py:-15},{n:12,py:-15},{n:13,py:-15},{n:14,py:-15}], ml:[] } },
    { name: '4C-3: 特殊ドーム構造', data: { nodes: [{x:0,y:0,s:'p'},{x:40,y:0,s:'r'},{x:5,y:3,s:'f'},{x:10,y:6,s:'f'},{x:15,y:9,s:'f'},{x:20,y:10,s:'f'},{x:25,y:9,s:'f'},{x:30,y:6,s:'f'},{x:35,y:3,s:'f'},{x:2.5,y:1.5,s:'f'},{x:37.5,y:1.5,s:'f'}], members:[
        {i:1,j:10, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},{i:10,j:3, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},{i:3,j:4, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},{i:4,j:5, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},{i:5,j:6, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},
        {i:6,j:7, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},{i:7,j:8, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},{i:8,j:9, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},{i:9,j:11, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4},{i:11,j:2, E:UNIT_CONVERSION.E_STEEL, I:1.10e-4, A:5.245e-3, Z:6.38e-4}
    ], nl:[{n:3,py:-10},{n:4,py:-10},{n:5,py:-10},{n:6,py:-10},{n:7,py:-10},{n:8,py:-10},{n:9,py:-10}], ml:[] } },
    { name: '4C-4: 多層メガストラクチャー', data: { nodes: [{x:0,y:0,s:'x'},{x:12,y:0,s:'x'},{x:24,y:0,s:'x'},{x:36,y:0,s:'x'},{x:48,y:0,s:'x'},{x:0,y:12,s:'f'},{x:12,y:12,s:'f'},{x:24,y:12,s:'f'},{x:36,y:12,s:'f'},{x:48,y:12,s:'f'},{x:0,y:24,s:'f'},{x:12,y:24,s:'f'},{x:24,y:24,s:'f'},{x:36,y:24,s:'f'},{x:48,y:24,s:'f'},{x:0,y:36,s:'f'},{x:12,y:36,s:'f'},{x:24,y:36,s:'f'},{x:36,y:36,s:'f'},{x:48,y:36,s:'f'},{x:0,y:48,s:'f'},{x:12,y:48,s:'f'},{x:24,y:48,s:'f'},{x:36,y:48,s:'f'},{x:48,y:48,s:'f'}], members: [
        {i:1,j:6, E:UNIT_CONVERSION.E_STEEL, I:6.66e-4, A:2.187e-2, Z:3.33e-3},{i:6,j:11, E:UNIT_CONVERSION.E_STEEL, I:6.66e-4, A:2.187e-2, Z:3.33e-3},{i:11,j:16, E:UNIT_CONVERSION.E_STEEL, I:5.61e-4, A:1.868e-2, Z:2.85e-3},{i:16,j:21, E:UNIT_CONVERSION.E_STEEL, I:5.61e-4, A:1.868e-2, Z:2.85e-3},
        {i:2,j:7, E:UNIT_CONVERSION.E_STEEL, I:6.66e-4, A:2.187e-2, Z:3.33e-3},{i:7,j:12, E:UNIT_CONVERSION.E_STEEL, I:6.66e-4, A:2.187e-2, Z:3.33e-3},{i:12,j:17, E:UNIT_CONVERSION.E_STEEL, I:5.61e-4, A:1.868e-2, Z:2.85e-3},{i:17,j:22, E:UNIT_CONVERSION.E_STEEL, I:5.61e-4, A:1.868e-2, Z:2.85e-3},
        {i:3,j:8, E:UNIT_CONVERSION.E_STEEL, I:6.66e-4, A:2.187e-2, Z:3.33e-3},{i:8,j:13, E:UNIT_CONVERSION.E_STEEL, I:6.66e-4, A:2.187e-2, Z:3.33e-3},{i:13,j:18, E:UNIT_CONVERSION.E_STEEL, I:5.61e-4, A:1.868e-2, Z:2.85e-3},{i:18,j:23, E:UNIT_CONVERSION.E_STEEL, I:5.61e-4, A:1.868e-2, Z:2.85e-3},
        {i:4,j:9, E:UNIT_CONVERSION.E_STEEL, I:6.66e-4, A:2.187e-2, Z:3.33e-3},{i:9,j:14, E:UNIT_CONVERSION.E_STEEL, I:6.66e-4, A:2.187e-2, Z:3.33e-3},{i:14,j:19, E:UNIT_CONVERSION.E_STEEL, I:5.61e-4, A:1.868e-2, Z:2.85e-3},{i:19,j:24, E:UNIT_CONVERSION.E_STEEL, I:5.61e-4, A:1.868e-2, Z:2.85e-3},
        {i:5,j:10, E:UNIT_CONVERSION.E_STEEL, I:6.66e-4, A:2.187e-2, Z:3.33e-3},{i:10,j:15, E:UNIT_CONVERSION.E_STEEL, I:6.66e-4, A:2.187e-2, Z:3.33e-3},{i:15,j:20, E:UNIT_CONVERSION.E_STEEL, I:5.61e-4, A:1.868e-2, Z:2.85e-3},{i:20,j:25, E:UNIT_CONVERSION.E_STEEL, I:5.61e-4, A:1.868e-2, Z:2.85e-3},
        {i:6,j:10, ...p_truss, A:6.291e-3},{i:11,j:15, ...p_truss, A:6.291e-3},{i:16,j:20, ...p_truss, A:6.291e-3},{i:21,j:25, ...p_truss, A:6.291e-3},
        {i:1,j:7, ...p_truss, A:6.291e-3},{i:2,j:6, ...p_truss, A:6.291e-3},{i:2,j:8, ...p_truss, A:6.291e-3},{i:3,j:7, ...p_truss, A:6.291e-3},
        {i:3,j:9, ...p_truss, A:6.291e-3},{i:4,j:8, ...p_truss, A:6.291e-3},{i:4,j:10, ...p_truss, A:6.291e-3},{i:5,j:9, ...p_truss, A:6.291e-3},
        {i:6,j:12, ...p_truss, A:6.291e-3},{i:7,j:11, ...p_truss, A:6.291e-3},{i:7,j:13, ...p_truss, A:6.291e-3},{i:8,j:12, ...p_truss, A:6.291e-3},
        {i:8,j:14, ...p_truss, A:6.291e-3},{i:9,j:13, ...p_truss, A:6.291e-3},{i:9,j:15, ...p_truss, A:6.291e-3},{i:10,j:14, ...p_truss, A:6.291e-3},
        {i:11,j:17, ...p_truss, A:4.678e-3},{i:12,j:16, ...p_truss, A:4.678e-3},{i:12,j:18, ...p_truss, A:4.678e-3},{i:13,j:17, ...p_truss, A:4.678e-3},
        {i:13,j:19, ...p_truss, A:4.678e-3},{i:14,j:18, ...p_truss, A:4.678e-3},{i:14,j:20, ...p_truss, A:4.678e-3},{i:15,j:19, ...p_truss, A:4.678e-3},
        {i:16,j:22, ...p_truss, A:4.678e-3},{i:17,j:21, ...p_truss, A:4.678e-3},{i:17,j:23, ...p_truss, A:4.678e-3},{i:18,j:22, ...p_truss, A:4.678e-3},
        {i:18,j:24, ...p_truss, A:4.678e-3},{i:19,j:23, ...p_truss, A:4.678e-3},{i:19,j:25, ...p_truss, A:4.678e-3},{i:20,j:24, ...p_truss, A:4.678e-3}
    ], nl:[{n:6,px:20},{n:7,px:20},{n:8,px:20},{n:9,px:20},{n:10,px:20},{n:11,px:20},{n:12,px:20},{n:13,px:20},{n:14,px:20},{n:15,px:20},{n:16,px:20},{n:17,px:20},{n:18,px:20},{n:19,px:20},{n:20,px:20},{n:21,px:20},{n:22,px:20},{n:23,px:20},{n:24,px:20},{n:25,px:20}], ml:[] } }
];

const loadPreset = (index) => {
        const preset = presets[index];
        if (!preset || !preset.data) return;
        const p = preset.data;
        historyStack = [];
        elements.nodesTable.innerHTML = '';
        elements.membersTable.innerHTML = '';
        elements.nodeLoadsTable.innerHTML = '';
        elements.memberLoadsTable.innerHTML = '';
        p.nodes.forEach(n => addRow(elements.nodesTable, [`#`, `<input type="number" value="${n.x}">`, `<input type="number" value="${n.y}">`, `<select><option value="free"${n.s==='f'?' selected':''}>自由</option><option value="pinned"${n.s==='p'?' selected':''}>ピン</option><option value="fixed"${n.s==='x'?' selected':''}>固定</option><option value="roller"${n.s==='r'?' selected':''}>ローラー</option></select>`], false));
        p.members.forEach(m => {
            const E_N_mm2 = m.E || '205000';
            const F_N_mm2 = m.F || '235';
            const I_m4 = m.I || 1e-9;
            const A_m2 = m.A || 1e-3;
            const Z_m3 = m.Z || 1e-9;
            addRow(elements.membersTable, [`#`, ...memberRowHTML(m.i, m.j, E_N_mm2, F_N_mm2, I_m4, A_m2, Z_m3, m.i_conn || m.ic, m.j_conn || m.jc)], false);
        });
        p.nl.forEach(l => addRow(elements.nodeLoadsTable, [`<input type="number" value="${l.n || l.node}">`, `<input type="number" value="${l.px||0}">`, `<input type="number" value="${l.py||0}">`, `<input type="number" value="${l.mz||0}">`], false));
        p.ml.forEach(l => addRow(elements.memberLoadsTable, [`<input type="number" value="${l.m || l.member}">`, `<input type="number" value="${l.w||0}">`], false));
        renumberTables();
        
        // ★★★★★ 修正箇所 ★★★★★
        // 描画範囲の自動調整フラグをリセット
        panZoomState.isInitialized = false; 
        
        drawOnCanvas();
        runFullAnalysis();
    };
    presets.forEach((p, i) => {
        const option = document.createElement('option');
        option.value = i;
        option.textContent = p.name;
        if (p.disabled) {
            option.disabled = true;
            option.style.fontWeight = 'bold';
            option.style.backgroundColor = '#eee';
        }
        elements.presetSelector.appendChild(option);
    });
    elements.presetSelector.addEventListener('change', (e) => {
        loadPreset(e.target.value);
    });

    elements.addNodeBtn.onclick = () => {
        const nodes = Array.from(elements.nodesTable.rows).map(row => ({
            x: parseFloat(row.cells[1].querySelector('input').value),
            y: parseFloat(row.cells[2].querySelector('input').value)
        }));
        let newX = 0, newY = 0;
        if(nodes.length > 0) {
            const maxX = Math.max(...nodes.map(n => n.x));
            const nodeAtMaxX = nodes.find(n => n.x === maxX);
            newX = maxX + parseFloat(elements.gridSpacing.value);
            newY = nodeAtMaxX.y;
        }
        addRow(elements.nodesTable, [`#`, `<input type="number" value="${newX.toFixed(2)}">`, `<input type="number" value="${newY.toFixed(2)}">`, `<select><option value="free">自由</option><option value="pinned">ピン</option><option value="fixed">固定</option><option value="roller">ローラー</option></select>`]);
    };
    elements.addMemberBtn.onclick = () => {
        const nodeCount = elements.nodesTable.rows.length;
        if (nodeCount < 2) {
            alert('部材を追加するには少なくとも2つの節点が必要です。');
            return;
        }
        const existingMembers = new Set();
        Array.from(elements.membersTable.rows).forEach(row => {
            const i = parseInt(row.cells[1].querySelector('input').value);
            const j = parseInt(row.cells[2].querySelector('input').value);
            existingMembers.add(`${Math.min(i,j)}-${Math.max(i,j)}`);
        });
        for (let i = 1; i <= nodeCount; i++) {
            for (let j = i + 1; j <= nodeCount; j++) {
                if (!existingMembers.has(`${i}-${j}`)) {
                    const I_m4 = parseFloat(newMemberDefaults.I) * 1e-8;
                    const A_m2 = parseFloat(newMemberDefaults.A) * 1e-4;
                    const Z_m3 = parseFloat(newMemberDefaults.Z) * 1e-6;
                    addRow(elements.membersTable, [`#`, ...memberRowHTML(i,j,newMemberDefaults.E,newMemberDefaults.F,I_m4,A_m2,Z_m3,newMemberDefaults.i_conn,newMemberDefaults.j_conn)]);
                    return;
                }
            }
        }
        alert('接続可能なすべての節点ペアは既に接続されています。');
    };
    elements.addNodeLoadBtn.onclick = () => { addRow(elements.nodeLoadsTable, ['<input type="number" value="1">', '<input type="number" value="0">', '<input type="number" value="0">', '<input type="number" value="0">']); };
    elements.addMemberLoadBtn.onclick = () => { addRow(elements.memberLoadsTable, ['<input type="number" value="1">', '<input type="number" value="0">']); };
    
    const saveInputData = () => {
        try {
            const state = getCurrentState();
            const csvSections = [];
            if (state.nodes.length > 0) {
                const header = 'x,y,support';
                const rows = state.nodes.map(n => `${n.x},${n.y},${n.support}`);
                csvSections.push('#NODES\n' + header + '\n' + rows.join('\n'));
            }
            if (state.members.length > 0) {
                const header = 'i,j,E,strengthType,strengthValue,I,A,Z,i_conn,j_conn,Zx,Zy,ix,iy';
                const rows = state.members.map(m => `${m.i},${m.j},${m.E},${m.strengthType},${m.strengthValue},${m.I},${m.A},${m.Z},${m.i_conn},${m.j_conn},${m.Zx || ''},${m.Zy || ''},${m.ix || ''},${m.iy || ''}`);
                csvSections.push('#MEMBERS\n' + header + '\n' + rows.join('\n'));
            }
            if (state.nodeLoads.length > 0) {
                const header = 'node,px,py,mz';
                const rows = state.nodeLoads.map(l => `${l.node},${l.px},${l.py},${l.mz}`);
                csvSections.push('#NODELOADS\n' + header + '\n' + rows.join('\n'));
            }
            if (state.memberLoads.length > 0) {
                const header = 'member,w';
                const rows = state.memberLoads.map(l => `${l.member},${l.w}`);
                csvSections.push('#MEMBERLOADS\n' + header + '\n' + rows.join('\n'));
            }
            const csvString = csvSections.join('\n\n');
            const blob = new Blob([csvString], { type: 'text/csv;charset=utf-8;' });
            const url = URL.createObjectURL(blob);
            const a = document.createElement('a');
            a.href = url;
            a.download = 'frame-model.csv';
            document.body.appendChild(a);
            a.click();
            document.body.removeChild(a);
            URL.revokeObjectURL(url);
        } catch (error) {
            alert('CSVデータの保存に失敗しました: ' + error.message);
        }
    };
    const loadInputData = () => {
        const fileInput = document.createElement('input');
        fileInput.type = 'file';
        fileInput.accept = '.csv,text/csv';
        fileInput.onchange = (e) => {
            const file = e.target.files[0];
            if (!file) return;
            const reader = new FileReader();
            reader.onload = (event) => {
                try {
                    const text = event.target.result;
                    const state = { nodes: [], members: [], nodeLoads: [], memberLoads: [] };
                    const sections = text.split(/#\w+\s*/).filter(s => s.trim() !== '');
                    const headers = text.match(/#\w+/g) || [];
                    if (headers.length === 0 || sections.length === 0) throw new Error('有効なセクション（#NODESなど）が見つかりませんでした。');
                    headers.forEach((header, index) => {
                        const sectionText = sections[index];
                        if (!sectionText) return;
                        const lines = sectionText.trim().split(/\r?\n/), headerLine = lines.shift(), keys = headerLine.split(',');
                        lines.forEach(line => {
                            if (!line.trim()) return;
                            const values = line.split(','), obj = {};
                            keys.forEach((key, i) => obj[key.trim()] = values[i] ? values[i].trim() : '');
                            if (header === '#NODES') state.nodes.push(obj);
                            else if (header === '#MEMBERS') state.members.push(obj);
                            else if (header === '#NODELOADS') state.nodeLoads.push(obj);
                            else if (header === '#MEMBERLOADS') state.memberLoads.push(obj);
                        });
                    });
                    if (state.nodes.length === 0 && state.members.length === 0) throw new Error('ファイルから有効なデータを読み込めませんでした。');
                    historyStack = [];
                    pushState();
                    restoreState(state);
                    runFullAnalysis();
                } catch (error) {
                    alert('CSVファイルの読み込みに失敗しました: ' + error.message);
                }
            };
            reader.readAsText(file);
        };
        fileInput.click();
    };
    const generateReport = () => {
        try {
            const modelCanvasImg=elements.modelCanvas.toDataURL('image/png');
            const displacementCanvasImg=elements.displacementCanvas.toDataURL('image/png');
            const momentCanvasImg=elements.momentCanvas.toDataURL('image/png');
            const axialCanvasImg=elements.axialCanvas.toDataURL('image/png');
            const shearCanvasImg=elements.shearCanvas.toDataURL('image/png');
            const ratioCanvasImg = elements.ratioCanvas.toDataURL('image/png');

            const reportWindow = window.open('', '_blank');
            reportWindow.document.write(`<html><head><title>構造解析レポート</title><style>body{font-family:sans-serif;margin:2em;}h1,h2,h3{color:#005A9C;border-bottom:2px solid #f0f8ff;padding-bottom:5px;}table{width:100%;border-collapse:collapse;margin-bottom:2em;}th,td{border:1px solid #ccc;padding:8px;text-align:center;}th{background-color:#f0f8ff;}img{max-width:100%;height:auto;border:1px solid #ccc;margin:1em 0;}.grid{display:grid;grid-template-columns:1fr;gap:20px;}.no-break{page-break-inside:avoid;}@media print{body{margin:1em;}button{display:none;}}</style></head><body><button onclick="window.print()">レポートを印刷</button><h1>構造解析レポート</h1><p>生成日時: ${new Date().toLocaleString()}</p><div class="no-break"><h2>モデル図</h2><img src="${modelCanvasImg}"></div><h2>入力データ</h2><div class="no-break"><h3>節点座標と境界条件</h3><table>${document.getElementById('nodes-table').innerHTML}</table></div><div class="no-break"><h3>部材 (物性値・接合条件)</h3><table>${document.getElementById('members-table').innerHTML}</table></div><div class="no-break"><h3>節点荷重</h3><table>${document.getElementById('node-loads-table').innerHTML}</table></div><div class="no-break"><h3>部材等分布荷重</h3><table>${document.getElementById('member-loads-table').innerHTML}</table></div><h2>計算結果</h2><div class="no-break grid"><div><h3>変位図</h3><img src="${displacementCanvasImg}"></div><div><h3>曲げモーメント図</h3><img src="${momentCanvasImg}"></div><div><h3>軸力図</h3><img src="${axialCanvasImg}"></div><div><h3>せん断力図</h3><img src="${shearCanvasImg}"></div></div><div class="no-break"><h3>節点変位</h3><table>${document.getElementById('displacement-results').innerHTML}</table></div><div class="no-break"><h3>支点反力</h3><table>${document.getElementById('reaction-results').innerHTML}</table></div><div class="no-break"><h3>部材端力</h3><table>${document.getElementById('force-results').innerHTML}</table></div><div class="no-break"><h2>断面算定結果</h2><h3>検定比図</h3><img src="${ratioCanvasImg}"><h3>検定比 詳細</h3><table>${document.getElementById('section-check-results').innerHTML}</table></div></body></html>`);
            reportWindow.document.close();
        } catch (e) {
            alert('レポートの生成に失敗しました: ' + e.message);
            console.error("Report generation failed: ", e);
        }
    };
    
    const runFullAnalysis = () => {
        calculate();
        runSectionCheck();
    };
    const runSectionCheck = () => {
        if (!lastResults) return;
        const selectedTerm = document.querySelector('input[name="load-term"]:checked').value;
        lastSectionCheckResults = calculateSectionCheck(selectedTerm);
        displaySectionCheckResults();
        drawRatioDiagram();
    };
    elements.calculateBtn.addEventListener('click', runFullAnalysis);
    elements.calculateAndAnimateBtn.addEventListener('click', () => {
        runFullAnalysis();
        if (lastResults && lastResults.D) {
            animateDisplacement(lastResults.nodes, lastResults.members, lastResults.D, lastResults.memberLoads);
        }
    });
    
    document.body.classList.remove('section-check-disabled');
    elements.loadTermRadios.forEach(radio => radio.addEventListener('change', () => {
        if (lastResults) {
            runSectionCheck();
        }
    }));
    
    elements.gridToggle.addEventListener('change', drawOnCanvas);
    elements.gridSpacing.addEventListener('change', drawOnCanvas);
    elements.saveBtn.addEventListener('click', saveInputData);
    elements.loadBtn.addEventListener('click', loadInputData);
    elements.reportBtn.addEventListener('click', generateReport);
    window.addEventListener('resize', drawOnCanvas);

    elements.autoScaleBtn.addEventListener('click', () => {
        panZoomState = { scale: 1, offsetX: 0, offsetY: 0, isInitialized: false };
        elements.modelCanvas.style.height = '500px';
        drawOnCanvas();
    });

    elements.resetModelBtn.addEventListener('click', () => {
        if (confirm('本当にモデル情報を全てリセットしますか？この操作は元に戻せません。')) {
            panZoomState.isInitialized = false;
            historyStack = [];
            elements.nodesTable.innerHTML = '';
            elements.membersTable.innerHTML = '';
            elements.nodeLoadsTable.innerHTML = '';
            elements.memberLoadsTable.innerHTML = '';
            clearResults();
            drawOnCanvas();
        }
    });
    
    // Initial Load
    loadPreset(15);
    elements.presetSelector.value = 15;
    setCanvasMode('select');
    toggleSectionCheckUI();

    function updateMemberProperties(memberIndex, props) {
        if (memberIndex >= 0 && memberIndex < elements.membersTable.rows.length) {
            const row = elements.membersTable.rows[memberIndex];
            const eSelect = row.cells[3].querySelector('select'), eInput = row.cells[3].querySelector('input[type="number"]');

            // E値の更新 (もしあれば)
            if (props.E) {
                const eValue = props.E.toString();
                eInput.value = eValue;
                eSelect.value = Array.from(eSelect.options).some(opt=>opt.value===eValue) ? eValue : 'custom';
                eInput.readOnly = eSelect.value !== 'custom';
                // E値の変更は強度入力欄の再生成をトリガーするため、changeイベントを発火させる
                eSelect.dispatchEvent(new Event('change'));
            }

            // ========== ここからが主要な修正点 ==========
            // props.F ではなく props.strengthValue をチェックし、タイプに応じて値を設定
            if (props.strengthValue) {
                // E値変更で再生成された後の要素を確実につかむため、少し待機する
                setTimeout(() => {
                    const strengthInputContainer = row.cells[4].firstElementChild;
                    if (strengthInputContainer) {
                        const s_input = strengthInputContainer.querySelector('input');
                        const s_select = strengthInputContainer.querySelector('select');
                        const s_type = props.strengthType;
                        const s_value = props.strengthValue;

                        if (s_type === 'wood-type') {
                            // 木材の場合：selectの値を更新
                            if(s_select) s_select.value = s_value;
                        } else {
                            // 鋼材、コンクリート、その他F値を持つ材料の場合
                            if(s_select && s_input) {
                                // プリセットに値が存在するかチェック
                                const isPreset = Array.from(s_select.options).some(opt => opt.value === s_value.toString());
                                if(isPreset) {
                                    s_select.value = s_value;
                                    s_input.value = s_value;
                                    s_input.readOnly = true;
                                } else {
                                    s_select.value = 'custom';
                                    s_input.value = s_value;
                                    s_input.readOnly = false;
                                }
                            }
                        }
                    }
                }, 0);
            }
            // ========== ここまでが主要な修正点 ==========
            
            row.cells[5].querySelector('input').value = props.I;
            row.cells[6].querySelector('input').value = props.A;
            if (props.Z) row.cells[7].querySelector('input').value = props.Z;
            
            if (props.Zx) row.dataset.zx = props.Zx;
            if (props.Zy) row.dataset.zy = props.Zy;
            if (props.ix) row.dataset.ix = props.ix;
            if (props.iy) row.dataset.iy = props.iy;
            
            // 変更を計算に反映させるためにchangeイベントを発火
            row.cells[5].querySelector('input').dispatchEvent(new Event('change', { bubbles: true }));
        } else {
            console.error(`無効な部材インデックス: ${memberIndex}`);
        }
    }


    window.addEventListener('storage', (e) => {
        if (e.key === 'steelSelectionForFrameAnalyzer' && e.newValue) {
            try {
                const data = JSON.parse(e.newValue);
                if (data && data.targetMemberIndex !== undefined && data.properties) {
                    updateMemberProperties(data.targetMemberIndex, data.properties);
                    localStorage.removeItem('steelSelectionForFrameAnalyzer');
                }
            } catch (error) {
                console.error('localStorageからのデータ解析に失敗しました:', error);
            }
        }
    });

    // モデル図のコンテナのリサイズを監視して再描画
    const modelCanvasContainer = document.querySelector('.input-section .canvas-container');
    if (modelCanvasContainer) {
        const resizeObserver = new ResizeObserver(() => {
            // リサイズ時に panZoomState をリセットしないように isInitialized フラグを維持
            const wasInitialized = panZoomState.isInitialized;
            panZoomState.isInitialized = false; // getDrawingContextで再計算させる
            drawOnCanvas();
            panZoomState.isInitialized = wasInitialized; // 状態を復元
        });
        resizeObserver.observe(modelCanvasContainer);
    }
});
