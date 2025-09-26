/**
 * フレーム解析ウィンドウ (親) から部材性能選択ウィンドウ (子) を開く関数
 * @param {number} memberIndex - 更新対象となる部材の行インデックス
 * @param {object} currentProps - 部材の現在のプロパティ { material, E, strengthValue }
 */
function openSteelSelector(memberIndex, currentProps = {}) {
    // URLにパラメータを追加して、材料の種類や現在の値を渡す
    const params = new URLSearchParams({
        targetMember: memberIndex,
        material: currentProps.material || 'steel',
        eValue: currentProps.E || '205000',
        strengthValue: currentProps.strengthValue || '235'
    });
    
    const url = `steel_selector.html?${params.toString()}`;
    const width = 1200;
    const height = 800;
    const left = (window.screen.width / 2) - (width / 2);
    const top = (window.screen.height / 2) - (height / 2);
    window.open(url, 'SteelSelector', `width=${width},height=${height},top=${top},left=${left}`);
}

/**
 * 部材性能選択ウィンドウ (子) から親ウィンドウにデータを送信する関数
 * localStorageを使用してデータを渡します。
 * @param {object} properties - { E, F, I, A, Z, Zx, Zy, ix, iy, strengthType, strengthValue } 等の形式のオブジェクト
 */
function sendDataToParent(properties) {
    const urlParams = new URLSearchParams(window.location.search);
    const targetMemberIndex = urlParams.get('targetMember');

    if (targetMemberIndex !== null) {
        const dataToSend = {
            targetMemberIndex: parseInt(targetMemberIndex, 10),
            properties: properties,
            timestamp: new Date().getTime() // 変更を検知するためのタイムスタンプ
        };
        
        // localStorageにデータを保存する
        localStorage.setItem('steelSelectionForFrameAnalyzer', JSON.stringify(dataToSend));
        
        // ウィンドウを閉じる
        window.close();
    } else {
        alert('送信先の部材が見つかりません。');
    }
}